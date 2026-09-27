;;; -*- Mode: LISP; Syntax: Common-Lisp; Package: GEM; Base: 10 -*-
;;;
;;; CL-XCB Device Backend for GEM (Garnet Extension Mechanism)
;;;
;;; Implements GEM device abstraction using cl-xcb (pure Common Lisp XCB).
;;;

(in-package :gem)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (use-package :xcb-const :gem))

;;; X11 angles are specified in 1/64ths of a degree.
(defconstant +deg-90*64+  (* 90 64))
(defconstant +deg-180*64+ (* 180 64))
(defconstant +deg-270*64+ (* 270 64))
(defconstant +deg-360*64+ (* 360 64))


;;; Connection, Screen, and Device State

(defvar *default-xcb-connection* nil
  "The primary XCB connection used by Garnet.")

(defvar *default-xcb-screen* nil
  "The primary XCB screen structure.")

(defvar *default-xcb-screen-number* 0
  "Screen number on the X server.")

(defvar *default-xcb-root* nil
  "The root window XID of the primary XCB screen.")

(defvar *default-xcb-colormap* nil
  "The default colormap XID.")

(defvar *screen-width* 1024
  "Width of the primary screen in pixels.")

(defvar *screen-height* 768
  "Height of the primary screen in pixels.")

(defvar *white* 1
  "White pixel value.")

(defvar *black* 0
  "Black pixel value.")

(defvar *color-screen-p* :true-color
  "Screen color capability (default true-color).")

(defvar *exposure-event-mask*
  ;; KeyPress | ButtonPress | Exposure | StructureNotify
  (logior +event-mask-key-press+
          +event-mask-button-press+
          +event-mask-exposure+
          +event-mask-structure-notify+)
  "Default event mask for newly created Garnet windows.")

;;; Table mapping XID (integer) -> Opal window schema
(defparameter *drawable-to-window-table* (make-hash-table :test 'eql))

;;; Pixmap table mapping XID -> Opal pixmap
(defparameter *pixmap-table* (make-hash-table :test 'eql))

;;; Font table mapping font name -> font XID
(defparameter *xcb-font-table* (make-hash-table :test 'equal))

;;; Font metrics cache mapping font XID -> xcb-font-metrics structure
(defparameter *xcb-font-metrics-table* (make-hash-table :test 'eql))


;; Graphics Context Structure & State

(defstruct xcb-image
  width
  height
  depth
  bits-per-pixel
  bytes-per-line
  data
  properties
  x-hot
  y-hot)

(defstruct (gem-gc (:print-function gem-gc-print-function))
  gcontext               ; XID (integer)
  opal-style             ; cached Opal line-style or filling-style schema
  function               ; cached integer (0-15)
  foreground             ; cached pixel integer
  background             ; cached pixel integer
  line-width             ; cached integer
  line-style             ; cached integer (0, 1, 2)
  cap-style              ; cached integer (0, 1, 2, 3)
  join-style             ; cached integer (0, 1, 2)
  dashes                 ; cached dashes
  font                   ; cached font XID
  fill-style             ; cached integer (0, 1, 2, 3)
  fill-rule              ; cached integer (0, 1)
  stipple                ; cached pixmap XID
  clip-mask              ; cached clip mask (:none or list of rects)
  stored-clip-mask)

(defun gem-gc-print-function (gc stream depth)
  (declare (ignore depth))
  (format stream "#<GEM-XCB-GC xid ~A fn ~A clip ~A>"
          (gem-gc-gcontext gc)
          (gem-gc-function gc)
          (gem-gc-clip-mask gc)))

;;; Cached graphic contexts for line and fill styles
(defvar *xcb-line-gc* nil)
(defvar *xcb-fill-gc* nil)

;;; Function mapping alist for raster ops
(defvar *function-alist* nil)
(defvar *copy* +gx-copy+)

;;; Display info structure for GEM
(defvar *display-info*
  (make-display-info
   :display nil
   :screen nil
   :root-window nil
   :line-style-gc nil
   :filling-style-gc nil))

;;; Macro to access XCB connection from an Opal window
(declaim (inline the-display get-full-display-name connection-for-window))

(defun the-display (window)
  "Given an Opal window, return the XCB connection attached to it."
  (if (and window (schema-p window))
      (let ((dinfo (g-value window :display-info)))
        (if dinfo
            (display-info-display dinfo)
            *default-xcb-connection*))
      *default-xcb-connection*))

;;; Device schema for cl-xcb
(create-schema 'xcb-device (:root-window *root-window*) (:device-type :xcb))

;;; Display specification parsing
(defun get-full-display-name ()
  "Determine the full DISPLAY environment string, defaulting to \":0\"."
  (or (uiop:getenv "DISPLAY") ":0"))

(defun get-display-number (display)
  "Extract the display number from a DISPLAY string like \":0.0\"."
  (let* ((colon-pos (position #\: display :from-end t))
         (period-pos (and colon-pos (position #\. display :start colon-pos))))
    (unless colon-pos
      (error "The display specification \"~A\" is ill-formed: missing colon" display))
    (let ((display-number
           (parse-integer (subseq display (1+ colon-pos) period-pos) :junk-allowed t)))
      (unless (numberp display-number)
        (error "The display specification \"~A\" is invalid: bad display number" display))
      display-number)))

(defun get-display-name (display)
  "Extract the host name part of a DISPLAY string."
  (let ((colon-pos (position #\: display :from-end t)))
    (if colon-pos
        (subseq display 0 colon-pos)
        display)))

(defun get-screen-number (display)
  "Extract the screen number from a DISPLAY string like \":0.0\"."
  (let* ((colon-pos (position #\: display :from-end t))
         (period-pos (and colon-pos
                          (position #\. display :start colon-pos))))
    (if period-pos
        (or (parse-integer (subseq display (1+ period-pos)) :junk-allowed t) 0)
        0)))

(defun connection-for-window (window)
  "Return the XCB connection associated with WINDOW or the current root."
  (the-display (or window (g-value gem:device-info :current-root))))


;;; GC Synchronization & Raster Operations

(defun xcb-resolve-function (function)
  "Resolve function keyword or object to standard X11 GX function number (0-15)."
  (cond
    ((numberp function) function)
    ((get function :xcb-draw-function))
    ((get function :x-draw-function))
    ((cdr (assoc function *function-alist*)))
    (t +gx-copy+)))

(defun xcb-line-style-val (style)
  (case style
    ((:solid nil) +line-style-solid+)
    ((:dash :on-off-dash) +line-style-on-off-dash+)
    (:double-dash +line-style-double-dash+)
    (t (if (numberp style) style +line-style-solid+))))

(defun xcb-cap-style-val (cap)
  (case cap
    (:not-last +cap-style-not-last+)
    ((:butt nil) +cap-style-butt+)
    (:round +cap-style-round+)
    (:projecting +cap-style-projecting+)
    (t (if (numberp cap) cap +cap-style-butt+))))

(defun xcb-join-style-val (join)
  (case join
    ((:miter nil) +join-style-miter+)
    (:round +join-style-round+)
    (:bevel +join-style-bevel+)
    (t (if (numberp join) join +join-style-miter+))))

(defun xcb-fill-style-val (style)
  (case style
    ((:solid nil) +fill-style-solid+)
    (:tiled +fill-style-tiled+)
    (:stippled +fill-style-stippled+)
    (:opaque-stippled +fill-style-opaque-stippled+)
    (t (if (numberp style) style +fill-style-solid+))))

(defun xcb-fill-rule-val (rule)
  (case rule
    ((:even-odd nil) +fill-rule-even-odd+)
    (:winding +fill-rule-winding+)
    (t (if (numberp rule) rule +fill-rule-even-odd+))))

(defun xcb-stage-gc-attribute (gem-gc slot value)
  "Update SLOT's cached value in GEM-GC without talking to the server.
Returns (VALUES CHANGED-P MASK-BIT KEYWORD VALUE).  MASK-BIT is NIL when
nothing has to be sent, either because the attribute did not change or
because the new value is not one the server needs (a stipple of 0).
:CLIP-MASK is not handled here; it needs its own request."
  (macrolet ((stage (accessor bit form)
               `(let ((v ,form))
                  (unless (eql v (,accessor gem-gc))
                    (setf (,accessor gem-gc) v)
                    (values t ,bit slot v)))))
    (case slot
      (:function   (stage gem-gc-function   +gc-function+   (xcb-resolve-function value)))
      (:foreground (stage gem-gc-foreground +gc-foreground+ (or value *black*)))
      (:background (stage gem-gc-background +gc-background+ (or value *white*)))
      (:line-width (stage gem-gc-line-width +gc-line-width+ (or value 0)))
      (:line-style (stage gem-gc-line-style +gc-line-style+ (xcb-line-style-val value)))
      (:cap-style  (stage gem-gc-cap-style  +gc-cap-style+  (xcb-cap-style-val value)))
      (:join-style (stage gem-gc-join-style +gc-join-style+ (xcb-join-style-val value)))
      (:fill-style (stage gem-gc-fill-style +gc-fill-style+ (xcb-fill-style-val value)))
      (:fill-rule  (stage gem-gc-fill-rule  +gc-fill-rule+  (xcb-fill-rule-val value)))
      (:stipple
       (let ((v (or value 0)))
         (unless (eql v (gem-gc-stipple gem-gc))
           (setf (gem-gc-stipple gem-gc) v)
           (values t (and (/= v 0) +gc-stipple+) slot v))))
      (:font
       (when (and value (not (eql value (gem-gc-font gem-gc))))
         (setf (gem-gc-font gem-gc) value)
         (values t +gc-font+ slot value))))))

(defun xcb-set-gc-clip-mask (conn gem-gc value)
  "Update GEM-GC's clip mask and send it if it changed.  Returns T if changed."
  (let ((gc-xid (gem-gc-gcontext gem-gc)))
    (cond
      ((or (null value) (eq value :none))
       (unless (eq (gem-gc-clip-mask gem-gc) :none)
         (setf (gem-gc-clip-mask gem-gc) :none)
         (xcb:change-gc conn gc-xid +gc-clip-mask+ :clip-mask +pixmap-none+)
         t))
      ((listp value)
       (unless (equal value (gem-gc-clip-mask gem-gc))
         (setf (gem-gc-clip-mask gem-gc) value)
         (let ((rects nil))
           (do ((cur value (cddddr cur)))
               ((null cur))
             (push (make-instance 'xcb:rectangle
                                  :x (first cur)
                                  :y (second cur)
                                  :width (max 1 (third cur))
                                  :height (max 1 (fourth cur)))
                   rects))
           (xcb:set-clip-rectangles conn 0 gc-xid 0 0 (nreverse rects)))
         t)))))

(defun xcb-set-gc-attribute (conn gem-gc slot value)
  "Update a slot in GEM-GC and emit XCB:CHANGE-GC if the attribute changed.
Returns T if the attribute was changed.  To change several attributes at
once, use WITH-XCB-GC-CHANGES, which sends a single request."
  (if (eq slot :clip-mask)
      (xcb-set-gc-clip-mask conn gem-gc value)
      (multiple-value-bind (changed bit key v)
          (xcb-stage-gc-attribute gem-gc slot value)
        (when bit
          (xcb:change-gc conn (gem-gc-gcontext gem-gc) bit key v))
        changed)))

(defmacro with-xcb-gc-changes ((stage-fn conn gem-gc) &body body)
  "Evaluate BODY with a local function (STAGE-FN SLOT VALUE) that updates
GEM-GC's cache like XCB-SET-GC-ATTRIBUTE and returns T if SLOT changed.
Every change staged in BODY is sent in a single ChangeGC request when BODY
exits, so the server-side GC always matches the cache.  :CLIP-MASK cannot be
staged."
  (let ((c (gensym "CONN")) (g (gensym "GC")) (mask (gensym "MASK")) (args (gensym "ARGS")))
    `(let ((,c ,conn) (,g ,gem-gc) (,mask 0) (,args '()))
       (flet ((,stage-fn (slot value)
                (multiple-value-bind (changed bit key v)
                    (xcb-stage-gc-attribute ,g slot value)
                  (when bit
                    (setf ,mask (logior ,mask bit)
                          ,args (list* key v ,args)))
                  changed)))
         (unwind-protect (progn ,@body)
           (unless (zerop ,mask)
             (apply #'xcb:change-gc ,c (gem-gc-gcontext ,g) ,mask ,args)))))))

(defun xcb-color-to-pixel (color &optional (default *black*))
  "Convert an Opal color schema or number to an X11 pixel integer."
  (if (and color (schema-p color))
      (or (g-value color :colormap-index)
          (let ((r (round (* (or (g-value color :red) 0.0) 255)))
                (g (round (* (or (g-value color :green) 0.0) 255)))
                (b (round (* (or (g-value color :blue) 0.0) 255))))
            (logior (ash r 16) (ash g 8) b)))
      (if (numberp color) color default)))

(defun set-xcb-line-style (conn line-style gem-gc root-window &optional (draw-fn +gx-copy+))
  (declare (ignore root-window))
  (when line-style
    (let ((fn (xcb-resolve-function draw-fn)))
      (with-xcb-gc-changes (stage conn gem-gc)
        (let ((draw-fn-changed? (stage :function fn)))
          ;; Like the CLX backend: with :no-op nothing is drawn, so skip the rest.
          (unless (eql fn +gx-noop+)
            (when (or draw-fn-changed?
                      (not (eq line-style (gem-gc-opal-style gem-gc))))
              (stage :foreground (xcb-color-to-pixel (g-value line-style :foreground-color) *black*))
              (stage :background (xcb-color-to-pixel (g-value line-style :background-color) *white*)))
            (unless (eq line-style (gem-gc-opal-style gem-gc))
              (setf (gem-gc-opal-style gem-gc) line-style)
              (stage :line-width (or (g-value line-style :line-thickness) 0))
              (stage :line-style (g-value line-style :line-style))
              (stage :cap-style (g-value line-style :cap-style))
              (stage :join-style (g-value line-style :join-style)))
            (stage :fill-style :solid)))))))

(defun xcb-get-stipple-pixmap (style-schema root-window)
  "Get or create an X11 depth-1 pixmap for a Garnet stipple filling style."
  (let ((stipple-schema (and style-schema (schema-p style-schema) (g-value style-schema :stipple))))
    (when stipple-schema
      (let ((root-plist (g-value stipple-schema :root-pixmap-plist)))
        (or (getf root-plist root-window)
            (let* ((the-image (or (g-value stipple-schema :image)
                                  (let ((pct (g-value stipple-schema :percent)))
                                    (when (numberp pct)
                                      (let ((idx (round (* (max 0 (min 100 pct)) 16) 100)))
                                        (xcb-device-image (or root-window *default-xcb-root*) idx)))))))
              (when the-image
                (let* ((w (if (xcb-image-p the-image) (xcb-image-width the-image) 16))
                       (h (if (xcb-image-p the-image) (xcb-image-height the-image) 16))
                       (pixmap (xcb-create-pixmap (or root-window *default-xcb-root*)
                                                  w h 1 the-image t)))
                  (s-value stipple-schema :root-pixmap-plist
                           (list* root-window pixmap root-plist))
                  pixmap))))))))

(defun set-xcb-filling-style (conn filling-style gem-gc root-window &optional (draw-fn +gx-copy+))
  (when filling-style
    (let ((fn (xcb-resolve-function draw-fn)))
      (with-xcb-gc-changes (stage conn gem-gc)
        ;; Like the CLX backend: with :no-op nothing is drawn, so only the
        ;; function is set.
        (unless (eql fn +gx-noop+)
          (when (or (stage :function fn)
                    (not (eq filling-style (gem-gc-opal-style gem-gc))))
            (stage :foreground (xcb-color-to-pixel (g-value filling-style :foreground-color) *black*))
            (stage :background (xcb-color-to-pixel (g-value filling-style :background-color) *white*)))
          (unless (eq filling-style (gem-gc-opal-style gem-gc))
            (setf (gem-gc-opal-style gem-gc) filling-style)
            (stage :fill-style (g-value filling-style :fill-style))
            (stage :fill-rule (g-value filling-style :fill-rule)))
          ;; Outside the UNLESS, as in CLX: the same filling style has a
          ;; different stipple pixmap on each root window.
          (let ((stipple (xcb-get-stipple-pixmap filling-style root-window)))
            (when stipple
              (stage :stipple stipple))))
        (stage :function fn)))))


;;; Device Initialization & Connection

(defun xcb-connect-and-handshake (&optional display-name)
  "Connect to X server and complete initial handshake using cl-xcb."
  (let ((display-str (or display-name (uiop:getenv "DISPLAY") ":0")))
    (multiple-value-bind (host display-number screen protocol)
        (xcb:parse-display display-str)
      (declare (ignore screen))
      (let ((display-socket (xcb:display-socket display-number)))
        (multiple-value-bind (family address number auth-name-raw auth-data-raw)
            (xcb:read-xauth host display-number :protocol protocol)
          (declare (ignore family address number))
          (let ((auth-name (or auth-name-raw ""))
                (auth-data (or auth-data-raw #())))
            (let ((conn (xcb:open-connection :path display-socket)))
              (xcb:setup-handshake conn auth-name auth-data)
              conn)))))))

(defun xcb-set-device-variables (full-display-name)
  "Open connection to X server using cl-xcb and initialize screen variables."
  (setf *default-xcb-screen-number* (get-screen-number full-display-name))
  (unless *x11-server-available*
    ;; Fallback values when X11 server is not available (e.g. non-GUI compilation)
    (setq *white* #xFFFFFF
          *black* 0)
    (return-from xcb-set-device-variables nil))
  (setf *default-xcb-connection* (xcb-connect-and-handshake full-display-name))
  (let ((roots (xcb:conn-roots *default-xcb-connection*)))
    (setf *default-xcb-screen*
          (if (< *default-xcb-screen-number* (length roots))
              (nth *default-xcb-screen-number* roots)
              (first roots)))
    (setf *screen-width* (xcb:width-in-pixels *default-xcb-screen*))
    (setf *screen-height* (xcb:height-in-pixels *default-xcb-screen*))
    (setf *default-xcb-root* (xcb:root *default-xcb-screen*))
    (setf *default-xcb-colormap* (xcb:default-colormap *default-xcb-screen*))
    (setf *white* (xcb:white-pixel *default-xcb-screen*))
    (setf *black* (xcb:black-pixel *default-xcb-screen*))

      ;; Allocate default GCs
      (let ((line-gc-xid (xcb:generate-id *default-xcb-connection*))
            (fill-gc-xid (xcb:generate-id *default-xcb-connection*)))
        ;; Create X11 GCs with foreground = black, background = white
        (xcb:create-gc *default-xcb-connection* line-gc-xid *default-xcb-root*
                       (logior +gc-foreground+ +gc-background+)
                       :foreground *black* :background *white*)
        (xcb:create-gc *default-xcb-connection* fill-gc-xid *default-xcb-root*
                       (logior +gc-foreground+ +gc-background+)
                       :foreground *black* :background *white*)

        (setf *xcb-line-gc*
              (make-gem-gc :gcontext line-gc-xid
                           :opal-style nil
                           :function +gx-copy+
                           :foreground *black*
                           :background *white*
                           :line-width 0
                           :line-style +line-style-solid+
                           :cap-style +cap-style-butt+
                           :join-style +join-style-miter+
                           :fill-style +fill-style-solid+
                           :fill-rule +fill-rule-even-odd+
                           :stipple nil
                           :clip-mask :none))

        (setf *xcb-fill-gc*
              (make-gem-gc :gcontext fill-gc-xid
                           :opal-style nil
                           :function +gx-copy+
                           :foreground *black*
                           :background *white*
                           :line-width 0
                           :line-style +line-style-solid+
                           :cap-style +cap-style-butt+
                           :join-style +join-style-miter+
                           :fill-style +fill-style-solid+
                           :fill-rule +fill-rule-even-odd+
                           :stipple nil
                           :clip-mask :none)))

      ;; Set up display-info
      (setf (display-info-display *display-info*) *default-xcb-connection*)
      (setf (display-info-screen *display-info*) *default-xcb-screen*)
      (setf (display-info-root-window *display-info*) *default-xcb-root*)
      (setf (display-info-line-style-gc *display-info*) *xcb-line-gc*)
      (setf (display-info-filling-style-gc *display-info*) *xcb-fill-gc*)

    ;; Initialize keyboard mapping
    (when (fboundp 'init-xcb-keyboard-mapping)
      (funcall 'init-xcb-keyboard-mapping *default-xcb-connection*)))
  t)

(defun xcb-set-screen-color-attribute-variables (root-window)
  (declare (ignore root-window))
  (setq *color-screen-p* :true-color))

(defun initialize-xcb-device-values (full-display-name root-window)
  (xcb-set-device-variables full-display-name)
  (xcb-set-screen-color-attribute-variables root-window))

(defun xcb-initialize-device-post ()
  "Post-initialization for cl-xcb: ensure atoms are interned."
  (when *default-xcb-connection*
    (xcb:intern-atom-id *default-xcb-connection* "WM_PROTOCOLS")
    (xcb:intern-atom-id *default-xcb-connection* "WM_DELETE_WINDOW")
    (xcb:intern-atom-id *default-xcb-connection* "_MOTIF_WM_HINTS")
    (xcb:intern-atom-id *default-xcb-connection* "GARNET_WINDOWS")))

(defun xcb-set-draw-function-alist (root-window)
  (declare (ignore root-window))
  ;; Standard X11 GX function numbers using xcb-const
  (setq *function-alist*
        `((:clear . ,+gx-clear+)
          (:and . ,+gx-and+)
          (:and-reverse . ,+gx-and-reverse+)
          (:copy . ,+gx-copy+)
          (:and-inverted . ,+gx-and-inverted+)
          (:no-op . ,+gx-noop+)
          (:xor . ,+gx-xor+)
          (:or . ,+gx-or+)
          (:nor . ,+gx-nor+)
          (:equiv . ,+gx-equiv+)
          (:invert . ,+gx-invert+)
          (:or-reverse . ,+gx-or-reverse+)
          (:copy-inverted . ,+gx-copy-inverted+)
          (:or-inverted . ,+gx-or-inverted+)
          (:nand . ,+gx-nand+)
          (:set . ,+gx-set+)))
  (setq *copy* +gx-copy+))

(defun xcb-set-draw-functions (root-window)
  (gem:set-draw-function-alist root-window)
  (dolist (fn-pair *function-alist*)
    (setf (get (car fn-pair) :xcb-draw-function) (cdr fn-pair))))

(defun init-xcb-device ()
  (attach-xcb-methods xcb-device)
  (s-value device-info :current-root *root-window*)
  (s-value device-info :current-device xcb-device)
  (pushnew xcb-device (g-value device-info :active-devices))
  (set-draw-functions *root-window*)
  *root-window*)

(defun init-xcb-device-post ()
  (initialize-xcb-device-values (get-full-display-name) *root-window*)
  (xcb-initialize-device-post)
  (s-value *root-window* :drawable (display-info-root-window *display-info*))
  (s-value *root-window* :display-info *display-info*))


;;; Window Lifecycle & Window Properties

(defun xcb-set-drawable-to-window (window drawable)
  (setf (gethash drawable *drawable-to-window-table*) window))

(defun xcb-drawable-to-window (root-window drawable)
  (declare (ignore root-window))
  (gethash drawable *drawable-to-window-table*))

(defun xcb-window-from-drawable (root-window drawable)
  (declare (ignore root-window))
  (gethash drawable *drawable-to-window-table*))

(defun xcb-connected-window-p (drawable)
  (let ((win (gethash drawable *drawable-to-window-table*)))
    (and win (schema-p win) win)))

(defun xcb-drawable-equal (root-window d1 d2)
  (declare (ignore root-window))
  (or (eql d1 d2)
      (and (numberp d1) (numberp d2) (= d1 d2))))

(defun xcb-check-wm-delete-window (root-window type data format)
  (and (eq format 32)
       (let ((conn (the-display (or root-window (g-value gem:device-info :current-root)))))
         (and conn
              (let ((wm-protocols (xcb:intern-atom-id conn "WM_PROTOCOLS"))
                    (wm-delete (xcb:intern-atom-id conn "WM_DELETE_WINDOW")))
                (and (= type wm-protocols)
                     (let ((atom-val (if (vectorp data)
                                         (aref data 0)
                                         (if (listp data) (car data) data))))
                       (= atom-val wm-delete))))))))

(defun xcb-create-window (parent-window
                          x y width height
                          title icon-name
                          background border-width
                          save-under visible
                          min-width min-height
                          max-width max-height
                          user-specified-position-p
                          user-specified-size-p
                          override-redirect)
  ;; VISIBLE is :NORMAL or :ICONIC, never NIL.  The window is not mapped here:
  ;; Opal maps it afterwards when its :VISIBLE slot is true, as with CLX.
  (declare (ignore visible))
  (let* ((display-info (g-value parent-window :display-info))
         (conn (display-info-display display-info))
         (screen (display-info-screen display-info))
         (parent-drawable (or (g-value parent-window :drawable)
                              (xcb:root screen)))
         (wid (xcb:generate-id conn))
         ;; Value mask: back-pixel | border-pixel | bit-gravity |
         ;; backing-store | override | save-under | event-mask
         (val-mask (logior +cw-back-pixel+
                           +cw-border-pixel+
                           +cw-bit-gravity+
                           +cw-backing-store+
                           +cw-override-redirect+
                           +cw-save-under+
                           +cw-event-mask+)))
    ;; Create X11 window
    (xcb:create-window conn
                       (xcb:root-depth screen)
                       wid
                       parent-drawable
                       x y
                       (max 1 width) (max 1 height)
                       (or border-width 0)
                       +window-class-input-output+
                       (xcb:root-visual screen)
                       val-mask
                       :background-pixel
                       (if (numberp background)
                           background
                           *white*)
                       :border-pixel *black*
                       :bit-gravity +gravity-north-west+
                       :backing-store +backing-store-always+
                       :override-redirect
                       (if override-redirect 1 0)
                       :save-under (if save-under 1 0)
                       :event-mask *exposure-event-mask*)

    ;; Set WM hints and properties
    (when title
      (xcb:set-wm-name conn wid (string title)))
    (when icon-name
      (xcb:set-wm-icon-name conn wid (string icon-name)))
    (xcb:set-wm-class conn wid "Opal" "Opal")
    (xcb:set-wm-delete-protocol conn wid)
    (let ((hints-args (list conn wid
                                :min-width  (or min-width  1)
                                :min-height (or min-height 1)
                                :max-width  (or max-width  #x7fff)
                                :max-height (or max-height #x7fff))))
      (when user-specified-position-p
        (setf hints-args (append hints-args (list :x x :y y))))
      (when user-specified-size-p
        (setf hints-args (append hints-args (list :width width :height height))))
      (apply #'xcb:set-wm-normal-hints hints-args))

    ;; Register in lookup table
    (xcb-set-drawable-to-window parent-window wid)

    wid))

(defun xcb-delete-window (root-window x-window)
  (let ((conn (connection-for-window root-window)))
    (when (and conn x-window)
      (remhash x-window *drawable-to-window-table*)
      (xcb-release-drawable conn x-window #'xcb:destroy-window))))

(defun xcb-map-and-wait (window drawable)
  (let ((conn (connection-for-window window)))
    (when (and conn drawable)
      (xcb:map-window conn drawable))))

(defun xcb-reparent (window new-parent drawable left top)
  (let* ((conn (the-display window))
         (parent-drawable (if new-parent
                              (g-value new-parent :drawable)
                              *default-xcb-root*)))
    (when (and conn drawable parent-drawable)
      (xcb:reparent-window
       conn drawable parent-drawable left top))))

(defun xcb-raise-or-lower (window raisep)
  (let* ((drawable (g-value window :drawable))
         (conn (the-display window)))
    (when (and conn drawable)
      (xcb:configure-window conn drawable +config-window-stack-mode+
                            :stack-mode
                            (if raisep
                                +stack-mode-above+
                                +stack-mode-below+)))))

(defun xcb-initialize-window-borders (window drawable)
  (declare (ignore drawable))
  (s-value window :left-border-width 0)
  (s-value window :top-border-width 0)
  (s-value window :right-border-width 0)
  (s-value window :bottom-border-width 0)
  (s-value window :total-border-width 0))

(defun xcb-set-window-property (window property value)
  (let* ((drawable (g-value window :drawable))
         (conn (the-display window)))
    (when (and conn drawable)
      (case property
        (:left
         (xcb:configure-window conn drawable +config-window-x+ :x value))
        (:top
         (xcb:configure-window conn drawable +config-window-y+ :y value))
        (:width
         (xcb:configure-window conn drawable +config-window-width+ :width (max 1 value)))
        (:height
         (xcb:configure-window conn drawable +config-window-height+ :height (max 1 value)))
        (:visible
         (if value
             (xcb:map-window conn drawable)
             (xcb:unmap-window conn drawable)))
        (:title
         (xcb:set-wm-name conn drawable (string value)))
        (:icon-name
         (xcb:set-wm-icon-name conn drawable (string value)))
        (:event-mask
         (let ((mask
                 (case value
                   (:E-K-M (logior +event-mask-exposure+
                                   +event-mask-structure-notify+
                                   +event-mask-key-press+
                                   +event-mask-button-press+
                                   +event-mask-button-release+
                                   +event-mask-pointer-motion+
                                   +event-mask-enter-window+
                                   +event-mask-leave-window+))
                   (:K-M   (logior +event-mask-exposure+
                                   +event-mask-structure-notify+
                                   +event-mask-key-press+
                                   +event-mask-button-press+
                                   +event-mask-button-release+
                                   +event-mask-pointer-motion+))
                   (:E-K   (logior +event-mask-exposure+
                                   +event-mask-structure-notify+
                                   +event-mask-key-press+
                                   +event-mask-button-press+
                                   +event-mask-button-release+
                                   +event-mask-enter-window+
                                   +event-mask-leave-window+))
                   (:K     (logior +event-mask-exposure+
                                   +event-mask-structure-notify+
                                   +event-mask-key-press+
                                   +event-mask-button-press+
                                   +event-mask-button-release+))
                   (t      (if (numberp value)
                               value
                               *exposure-event-mask*)))))
           (xcb:change-window-attributes
            conn drawable +cw-event-mask+ :event-mask mask)))
        (:cursor
         (xcb:change-window-attributes
          conn drawable +cw-cursor+ :cursor (or value +cursor-none+)))
        (:buffer-gcontext
         ;; VALUE is (BUFFER FOREGROUND BACKGROUND).  The GC is kept as a
         ;; GEM-GC, so XCB-CLEAR-AREA knows the background to clear with.
         (destructuring-bind (buffer foreground background) value
           (let ((gc-xid (xcb:generate-id conn)))
             (xcb:create-gc conn gc-xid buffer
                            (logior +gc-function+ +gc-foreground+ +gc-background+)
                            :function +gx-copy+
                            :foreground foreground
                            :background background)
             (s-value window :buffer-gcontext
                      (make-gem-gc :gcontext gc-xid
                                   :function +gx-copy+
                                   :foreground foreground
                                   :background background)))))
        (:background-color
         ;; Opal also sends :ON/:OFF here for :SAVE-UNDER; those are not colors.
         (when (or (null value) (schema-p value))
           (let ((pixel (xcb-color-to-index window value))
                 (buffer-gc (g-value window :buffer-gcontext)))
             (xcb:change-window-attributes conn drawable +cw-back-pixel+
                                           :background-pixel pixel)
             (when buffer-gc
               (xcb-set-gc-attribute conn buffer-gc :background pixel)))))))
    nil))

(defun xcb-translate-coordinates (root-window window1 x y &optional window2)
  (let* ((conn (connection-for-window (or root-window window1)))
         (src-win (if (numberp window1)
                      window1
                      (g-value window1 :drawable)))
         (dst-win (if window2
                      (if (numberp window2)
                          window2
                          (g-value window2 :drawable))
                      (xcb:root (first (xcb:conn-roots conn)))))
         (cookie (xcb:translate-coordinates conn src-win dst-win x y))
         (reply (xcb:translate-coordinates-reply conn cookie)))
    (values (xcb:dst-x reply) (xcb:dst-y reply))))

(defun xcb-mouse-grab (window grabp want-enter-leave &optional (ownerp t))
  (let* ((drawable (g-value window :drawable))
         (conn (the-display window)))
    (when (and conn drawable)
      (if grabp
          (let ((mask (if want-enter-leave
                          (logior +event-mask-button-press+
                                  +event-mask-button-release+
                                  +event-mask-pointer-motion+
                                  +event-mask-enter-window+
                                  +event-mask-leave-window+)
                          (logior +event-mask-button-press+
                                  +event-mask-button-release+
                                  +event-mask-pointer-motion+))))
            (if (eq ownerp :CHANGE)
                (xcb:change-active-pointer-grab conn +cursor-none+ +time-current-time+ mask)
                (xcb:grab-pointer conn (if ownerp 1 0) drawable mask
                                  +grab-mode-async+ +grab-mode-async+
                                  +window-none+ +cursor-none+ +time-current-time+)))
          (xcb:ungrab-pointer conn +time-current-time+)))))

(defun xcb-window-debug-id (window)
  (g-value window :drawable))

(defun xcb-window-depth (window)
  (or (g-value window :depth) 24))

(defun xcb-window-has-grown (window width height)
  "Returns true if the window's old buffer was smaller than the new width and height."
  (let ((old-buffer (g-value window :buffer)))
    (when old-buffer
      (let ((dims (gethash old-buffer *pixmap-table*)))
        (and dims
             (or (> width (first dims))
                 (> height (second dims))))))))

(defun xcb-device-batch-changes (root-window drawable function)
  (declare (ignore root-window drawable))
  (funcall function))

(defun xcb-flush-output (window)
  (let ((conn (the-display window)))
    (when conn
      (finish-output (xcb:conn-stream conn)))))

(defun xcb-beep (root-window)
  (let ((conn (the-display (or root-window (g-value gem:device-info :current-root)))))
    (when conn
      (xcb:bell conn 0)
      (finish-output (xcb:conn-stream conn)))))

(defun xcb-all-garnet-windows ()
  (let ((result nil))
    (maphash (lambda (k v) (declare (ignore k)) (pushnew v result))
             *drawable-to-window-table*)
    result))

(defun xcb-black-white-pixel (window)
  "Returns the black and white pixel for the screen of <window>, as multiple values."
  (if *x11-server-available*
      (let ((screen (or (and window (schema-p window)
                             (let ((dinfo (g-value window :display-info)))
                               (and dinfo (display-info-screen dinfo))))
                        *default-xcb-screen*)))
        (if screen
            (values (xcb:black-pixel screen)
                    (xcb:white-pixel screen))
            (values *black* *white*)))
      (values 0 1)))

(defun xcb-color-to-index (root-window a-color)
  (if a-color
      (or (g-value a-color :colormap-index)
          (let ((r (round (* (or (g-value a-color :red)   0.0) 255)))
                (g (round (* (or (g-value a-color :green) 0.0) 255)))
                (b (round (* (or (g-value a-color :blue)  0.0) 255))))
            (logior (ash r 16) (ash g 8) b)))
      (if (and root-window *x11-server-available*)
          (let ((screen (if (and root-window (schema-p root-window))
                            (let ((dinfo (g-value root-window :display-info)))
                              (and dinfo (display-info-screen dinfo)))
                            *default-xcb-screen*)))
            (if screen (xcb:white-pixel screen) *white*))
          *white*)))

(defun xcb-colormap-property (root-window property &optional a b c)
  (declare (ignore root-window a b c))
  (case property
    (:color-lookup (values 0 0 0))
    (:make-color 0)))

(defun xcb-query-color (root-window pixel)
  (declare (ignore root-window))
  (values (ash (logand pixel #xff0000) -16)
          (ash (logand pixel #x00ff00) -8)
          (logand pixel #x0000ff)))


;;; Shape Rendering & Drawing Primitives

(defun xcb-clear-area (window &optional (x 0) (y 0) width height clear-buffer-p)
  "Clear an area of WINDOW to its background.  If CLEAR-BUFFER-P, clear its
double buffer instead: the whole buffer when X is NIL."
  (let ((conn (the-display window)))
    (when conn
      (if clear-buffer-p
          (let ((buffer (g-value window :buffer))
                (buffer-gc (g-value window :buffer-gcontext)))
            (when (and buffer buffer-gc)
              ;; Pixmaps have no background, so fill with the GC's background.
              ;; Besides this, the buffer GC is only used by XCB-BIT-BLIT,
              ;; which does not use the foreground.
              (with-xcb-gc-changes (stage conn buffer-gc)
                (stage :function +gx-copy+)
                (stage :foreground (gem-gc-background buffer-gc)))
              (let ((rect (if x
                              (make-instance 'xcb:rectangle
                                             :x x :y y :width width :height height)
                              (destructuring-bind (w h &rest depth)
                                  (gethash buffer *pixmap-table*)
                                (declare (ignore depth))
                                (make-instance 'xcb:rectangle
                                               :x 0 :y 0 :width w :height h)))))
                (xcb:poly-fill-rectangle conn buffer (gem-gc-gcontext buffer-gc)
                                         (list rect)))))
          ;; ClearArea works on windows only, so never on the buffer.
          (let ((drawable (g-value window :drawable)))
            (when drawable
              (xcb:clear-area conn 0 drawable (or x 0) (or y 0)
                              (or width (g-value window :width))
                              (or height (g-value window :height)))))))))

(defun xcb-draw-rectangle (window left top width height function
                          line-style fill-style)
  (declare (fixnum left top width height))
  (if (< width 1) (setf width 1))
  (if (< height 1) (setf height 1))
  (let* ((display-info (g-value window :display-info))
         (conn (display-info-display display-info))
         (root-window (display-info-root-window display-info))
         (drawable (the-drawable window))
         (thickness (if line-style
                        (max (g-value line-style :line-thickness) 1)
                        0)))
    (if fill-style
        (let* ((gem-gc (display-info-filling-style-gc display-info))
               (gc-xid (gem-gc-gcontext gem-gc))
               (th2 (* 2 thickness)))
          (set-xcb-filling-style conn fill-style gem-gc root-window function)
          (let ((rect (make-instance 'xcb:rectangle
                                     :x (+ left thickness)
                                     :y (+ top thickness)
                                     :width (max 0 (- width th2))
                                     :height (max 0 (- height th2)))))
            (xcb:poly-fill-rectangle conn drawable gc-xid (list rect)))))
    (if line-style
        (let* ((gem-gc (display-info-line-style-gc display-info))
               (gc-xid (gem-gc-gcontext gem-gc))
               (half-thickness (truncate thickness 2)))
          (set-xcb-line-style conn line-style gem-gc root-window function)
          (let ((rect (make-instance 'xcb:rectangle
                                     :x (+ left half-thickness)
                                     :y (+ top half-thickness)
                                     :width (max 0 (- width thickness))
                                     :height (max 0 (- height thickness)))))
            (xcb:poly-rectangle conn drawable gc-xid (list rect)))))))

(defun xcb-draw-line (window x1 y1 x2 y2 function line-style &optional drawable)
  (let* ((display-info (g-value window :display-info))
         (conn (display-info-display display-info))
         (root-window (display-info-root-window display-info)))
    (unless drawable
      (setf drawable (the-drawable window)))
    (if line-style
        (let* ((gem-gc (display-info-line-style-gc display-info))
               (gc-xid (gem-gc-gcontext gem-gc)))
          (set-xcb-line-style conn line-style gem-gc root-window function)
          (let ((seg (make-instance 'xcb:segment :x1 x1 :y1 y1 :x2 x2 :y2 y2)))
            (xcb:poly-segment conn drawable gc-xid (list seg)))))))

;;; Scratch vector of XCB:POINT instances reused by XCB-POINTS-FROM-LIST, so
;;; drawing polylines does not allocate once it has grown to the largest
;;; polyline drawn.  Garnet draws from a single thread.
(defvar *xcb-point-scratch*
  (make-array 64 :fill-pointer 0 :adjustable t :initial-element nil))

(defun xcb-points-from-list (point-list)
  "Convert flat coordinate list (x0 y0 x1 y1 ...) into a vector of XCB:POINT
instances, or NIL if there are no points.  The vector and its points are
reused by the next call, so the result must not be kept."
  (let ((v *xcb-point-scratch*))
    (setf (fill-pointer v) 0)
    (do ((cur point-list (cddr cur)))
        ((null cur))
      (let ((x (car cur))
            (y (cadr cur)))
        (when (and x y)
          (let* ((i (fill-pointer v))
                 ;; Slots added when the vector grows are not initialized
                 ;; to NIL (SBCL fills them with 0), so test the type.
                 (p (and (< i (array-dimension v 0)) (aref v i))))
            (if (typep p 'xcb:point)
                (setf (slot-value p 'xcb::x) x
                      (slot-value p 'xcb::y) y
                      (fill-pointer v) (1+ i))
                (vector-push-extend (make-instance 'xcb:point :x x :y y) v))))))
    (and (plusp (fill-pointer v)) v)))

(defun xcb-draw-lines (window point-list function line-style fill-style)
  (let* ((display-info (g-value window :display-info))
         (conn (display-info-display display-info))
         (root-window (display-info-root-window display-info))
         (drawable (the-drawable window))
         (points (xcb-points-from-list point-list)))
    (when points
      (when fill-style
        (let* ((gem-gc (display-info-filling-style-gc display-info))
               (gc-xid (gem-gc-gcontext gem-gc)))
          (set-xcb-filling-style conn fill-style gem-gc root-window function)
          (xcb:fill-poly conn drawable gc-xid 0 0 points)))
      (when line-style
        (let* ((gem-gc (display-info-line-style-gc display-info))
               (gc-xid (gem-gc-gcontext gem-gc)))
          (set-xcb-line-style conn line-style gem-gc root-window function)
          (xcb:poly-line conn 0 drawable gc-xid points))))))

(defun xcb-draw-points (window point-list function line-style)
  (let* ((display-info (g-value window :display-info))
         (conn (display-info-display display-info))
         (root-window (display-info-root-window display-info))
         (drawable (the-drawable window))
         (points (xcb-points-from-list point-list)))
    (when (and line-style points)
      (let* ((gem-gc (display-info-line-style-gc display-info))
             (gc-xid (gem-gc-gcontext gem-gc)))
        (set-xcb-line-style conn line-style gem-gc root-window function)
        (xcb:poly-point conn 0 drawable gc-xid points)))))

(defconstant +rad-to-64th-deg+ (/ (* 180 64) pi)
  "Conversion factor from radians to 1/64ths of a degree.")

(defun xcb-angle (rad)
  "Convert radians to 1/64ths of a degree integer used by X11."
  (round (* rad +rad-to-64th-deg+)))

(defun xcb-draw-arc (window x y width height angle1 angle2 function
                    line-style fill-style &optional pie-slice-p)
  (declare (ignore pie-slice-p))
  (let* ((thickness (if line-style (max 1 (g-value line-style :line-thickness)) 0))
         (thickness2 (* thickness 2))
         (fill-width (max 0 (- width thickness2)))
         (fill-height (max 0 (- height thickness2)))
         (display-info (g-value window :display-info))
         (conn (display-info-display display-info))
         (root-window (display-info-root-window display-info))
         (drawable (the-drawable window))
         (a1 (xcb-angle angle1))
         (a2 (xcb-angle angle2)))
    (when fill-style
      (let* ((gem-gc (display-info-filling-style-gc display-info))
             (gc-xid (gem-gc-gcontext gem-gc))
             (arc (make-instance 'xcb:arc
                                 :x (+ x thickness)
                                 :y (+ y thickness)
                                 :width fill-width
                                 :height fill-height
                                 :angle1 a1
                                 :angle2 a2)))
        (set-xcb-filling-style conn fill-style gem-gc root-window function)
        (xcb:poly-fill-arc conn drawable gc-xid (list arc))))
    (when line-style
      (let* ((gem-gc (display-info-line-style-gc display-info))
             (gc-xid (gem-gc-gcontext gem-gc))
             (half-thickness (truncate thickness 2))
             (arc (make-instance 'xcb:arc
                                 :x (+ x half-thickness)
                                 :y (+ y half-thickness)
                                 :width (max 0 (- width thickness))
                                 :height (max 0 (- height thickness))
                                 :angle1 a1
                                 :angle2 a2)))
        (set-xcb-line-style conn line-style gem-gc root-window function)
        (xcb:poly-arc conn drawable gc-xid (list arc))))))

(defun xcb-draw-roundtangle (window left top width height
                             x-radius y-radius function
                             line-style fill-style)
  (let* ((display-info (g-value window :display-info))
         (conn (display-info-display display-info))
         (root-window (display-info-root-window display-info))
         (drawable (the-drawable window))
         (th (if line-style (max 1 (g-value line-style :line-thickness)) 0))
         (th/2 (floor th 2))
         (th\2 (ceiling th 2))
         (c-w (+ x-radius x-radius))
         (c-h (+ y-radius y-radius)))
    (when fill-style
      (let* ((gem-gc (display-info-filling-style-gc display-info))
             (gc-xid (gem-gc-gcontext gem-gc))
             (r x-radius)
             (top-l (+ top y-radius))
             (top-f (+ top th))
             (right-l (- (+ left width) r))
             (side-w (max 0 (- x-radius th)))
             (side-h (- height y-radius y-radius))
             (bottom-t (+ top height (- c-h))))
        (set-xcb-filling-style conn fill-style gem-gc root-window function)
        ;; Center rectangle and two side rectangles
        (let ((rects (list (make-instance 'xcb:rectangle
                                          :x (+ left r) :y top-f
                                          :width (- width r r) :height (max 0 (- height th th)))
                           (make-instance 'xcb:rectangle
                                          :x (+ left th) :y top-l
                                          :width side-w :height side-h)
                           (make-instance 'xcb:rectangle
                                          :x right-l :y top-l
                                          :width side-w :height side-h))))
          (xcb:poly-fill-rectangle conn drawable gc-xid rects))
        ;; Four filled corner arcs (90 degrees each = 5760 units)
        (let* ((right-f (+ (- right-l x-radius) th))
               (left-f (+ left th))
               (left-f-1 (- left-f (if line-style 1 0)))
               (top-f-1 (- top-f (if line-style 1 0)))
               (bottom-f (+ bottom-t th))
               (th2 (+ th th))
               (c-w-f (max 0 (- c-w th2)))
               (c-h-f (max 0 (- c-h th2)))
               (c-w-f+1 (+ c-w-f (if line-style 1 0)))
               (c-h-f+1 (+ c-h-f (if line-style 1 0)))
               (arcs (list (make-instance 'xcb:arc :x right-f :y top-f-1
                                                   :width c-w-f :height c-h-f+1
                                                   :angle1 0 :angle2 +deg-90*64+)
                           (make-instance 'xcb:arc :x (- left-f 1) :y (- top-f 1)
                                                   :width (+ c-w-f 1) :height (+ c-h-f 1)
                                                   :angle1 +deg-90*64+ :angle2 +deg-90*64+)
                           (make-instance 'xcb:arc :x left-f-1 :y bottom-f
                                                   :width c-w-f+1 :height c-h-f
                                                   :angle1 +deg-180*64+ :angle2 +deg-90*64+)
                           (make-instance 'xcb:arc :x right-f :y bottom-f
                                                   :width c-w-f :height c-w-f
                                                   :angle1 +deg-270*64+ :angle2 +deg-90*64+))))
          (xcb:poly-fill-arc conn drawable gc-xid arcs))))
    (when line-style
      (let* ((gem-gc (display-info-line-style-gc display-info))
             (gc-xid (gem-gc-gcontext gem-gc))
             (left-w (+ left x-radius))
             (right (+ left width (- x-radius)))
             (y (+ top th/2))
             (y1 (+ top height (- th\2)))
             (l (+ left th/2))
             (l1 (+ left width (- th\2)))
             (up (+ top y-radius))
             (down (+ top height (- y-radius)))
             (c-w-line (max 0 (- c-w th)))
             (c-h-line (max 0 (- c-h th))))
        (set-xcb-line-style conn line-style gem-gc root-window function)
        ;; Four border segments
        (let ((segs (list (make-instance 'xcb:segment :x1 left-w :y1 y :x2 right :y2 y)
                          (make-instance 'xcb:segment :x1 left-w :y1 y1 :x2 right :y2 y1)
                          (make-instance 'xcb:segment :x1 l :y1 up :x2 l :y2 down)
                          (make-instance 'xcb:segment :x1 l1 :y1 up :x2 l1 :y2 down))))
          (xcb:poly-segment conn drawable gc-xid segs))
        ;; Four corner arcs
        (let* ((arc-left (+ left th\2 (if (< th 2) -1 0)))
               (arc-right (+ left width (- c-w-line) (- th\2) (if (< th 2) 0 -1)))
               (arc-bottom (+ top height (- c-h-line) (- th\2) (if (<= th 3) 0 -1)))
               (arcs (list (make-instance 'xcb:arc :x arc-right :y (+ top th/2)
                                                   :width c-w-line :height c-h-line
                                                   :angle1 0 :angle2 +deg-90*64+)
                           (make-instance 'xcb:arc :x arc-left :y (+ top th/2)
                                                   :width c-w-line :height c-h-line
                                                   :angle1 +deg-90*64+ :angle2 +deg-90*64+)
                           (make-instance 'xcb:arc :x arc-left :y arc-bottom
                                                   :width c-w-line :height c-h-line
                                                   :angle1 +deg-180*64+ :angle2 +deg-90*64+)
                           (make-instance 'xcb:arc :x arc-right :y arc-bottom
                                                   :width c-w-line :height c-h-line
                                                   :angle1 +deg-270*64+ :angle2 +deg-90*64+))))
          (xcb:poly-arc conn drawable gc-xid arcs))))))

(defun xcb-set-clip-mask (window clip-mask &optional lstyle-ogc fstyle-ogc)
  (let* ((conn (the-display (or window (g-value gem:device-info :current-root))))
         (l-gc (or lstyle-ogc *xcb-line-gc*))
         (f-gc (or fstyle-ogc *xcb-fill-gc*)))
    (when (and conn l-gc)
      (xcb-set-gc-attribute conn l-gc :clip-mask clip-mask))
    (when (and conn f-gc)
      (xcb-set-gc-attribute conn f-gc :clip-mask clip-mask))))

(defun xcb-bit-blit (window source s-x s-y width height destination d-x d-y)
  (let* ((conn (the-display window))
         (gc-xid (gem-gc-gcontext (or (g-value window :buffer-gcontext)
                                      *xcb-line-gc*))))
    (when (and conn source destination)
      (xcb:copy-area conn source destination gc-xid s-x s-y d-x d-y width height))))


;;; Fonts and Text Operations with xcb-truetype

(defparameter *xcb-truetype-initialized-p* nil)
(defparameter *xcb-font-cache-table* (make-hash-table :test 'equal))
(defparameter *drawable-xft-table* (make-hash-table :test 'eql))

(defun ensure-xcb-truetype-initialized ()
  "Ensure xcb-truetype has indexed available system fonts."
  (unless *xcb-truetype-initialized-p*
    (xcb-truetype:cache-fonts)
    (setf *xcb-truetype-initialized-p* t)))

(defun xcb-resolve-font-family-and-subfamily (family face)
  "Resolve Garnet family and face keywords to an installed TrueType family and subfamily."
  (ensure-xcb-truetype-initialized)
  (let* ((all-fams (xcb-truetype:get-font-families))
         (fam (cond
                ((stringp family)
                 (or (find family all-fams :test #'string-equal)
                     (first all-fams)))
                ((eq family :serif)
                 (or (find "DejaVu Serif" all-fams :test #'string-equal)
                     (find "Liberation Serif" all-fams :test #'string-equal)
                     (first all-fams)))
                ((eq family :sans-serif)
                 (or (find "DejaVu Sans" all-fams :test #'string-equal)
                     (find "Liberation Sans" all-fams :test #'string-equal)
                     (first all-fams)))
                (t ; :fixed
                 (or (find "DejaVu Sans Mono" all-fams :test #'string-equal)
                     (find "Liberation Mono" all-fams :test #'string-equal)
                     (first all-fams)))))
         (available-subs (xcb-truetype:get-font-subfamilies fam))
         (target-sub (case face
                       (:bold (or (find "Bold" available-subs :test #'string-equal)
                                  (first available-subs)))
                       (:italic (or (find "Italic" available-subs :test #'string-equal)
                                    (find "Oblique" available-subs :test #'string-equal)
                                    (first available-subs)))
                       (:bold-italic (or (find "Bold Italic" available-subs :test #'string-equal)
                                         (find "Bold Oblique" available-subs :test #'string-equal)
                                         (first available-subs)))
                       (t (or (find "Regular" available-subs :test #'string-equal)
                              (find "Book" available-subs :test #'string-equal)
                              (first available-subs))))))
    (values fam (or target-sub (first available-subs)))))

(defun xcb-make-truetype-font (family face size)
  (multiple-value-bind (fam sub) (xcb-resolve-font-family-and-subfamily family face)
    (let ((sz (cond
                ((numberp size) size)
                ((eq size :small) 10)
                ((eq size :medium) 12)
                ((eq size :large) 16)
                ((eq size :very-large) 20)
                (t 12))))
      (make-instance 'xcb-truetype:font
                     :family fam
                     :subfamily sub
                     :size sz
                     :antialias t))))

(defun xcb-font-to-internal (root-window opal-font)
  "Convert a Garnet font schema (or descriptor) into an xcb-truetype:font instance."
  (declare (ignore root-window))
  (ensure-xcb-truetype-initialized)
  (cond
    ((typep opal-font 'xcb-truetype:font)
     opal-font)
    ((and opal-font (schema-p opal-font))
     (let* ((fam (or (g-value opal-font :family) :fixed))
            (fac (or (g-value opal-font :face) :roman))
            (sz  (or (g-value opal-font :size) :medium))
            (key (list fam fac sz)))
       (or (gethash key *xcb-font-cache-table*)
           (let ((inst (xcb-make-truetype-font fam fac sz)))
             (setf (gethash key *xcb-font-cache-table*) inst)
             (s-value opal-font :xfont inst)
             inst))))
    ((listp opal-font)
     (let ((key (list (first opal-font) (second opal-font) (third opal-font))))
       (or (gethash key *xcb-font-cache-table*)
           (setf (gethash key *xcb-font-cache-table*)
                 (xcb-make-truetype-font (first opal-font)
                                         (second opal-font)
                                         (third opal-font))))))
    ((stringp opal-font)
     (or (gethash opal-font *xcb-font-cache-table*)
         (setf (gethash opal-font *xcb-font-cache-table*)
               (xcb-make-truetype-font :fixed :roman :medium))))
    (t
     (or (gethash :default *xcb-font-cache-table*)
         (setf (gethash :default *xcb-font-cache-table*)
               (xcb-make-truetype-font :fixed :roman :medium))))))

(defun xcb-resolve-font (root-window font)
  (if (typep font 'xcb-truetype:font)
      font
      (or (and (schema-p font) (g-value font :xfont))
          (xcb-font-to-internal root-window font))))

(defun xcb-font-exists-p (root-window name)
  (declare (ignore root-window))
  (ensure-xcb-truetype-initialized)
  (not (null (find (string name) (xcb-truetype:get-font-families) :test #'string-equal))))

(defun xcb-font-name-p (root-window arg)
  (declare (ignore root-window))
  (or (stringp arg) (and (schema-p arg) (is-a-p arg opal::font))))

(defun xcb-make-font-name (root-window key)
  (declare (ignore root-window))
  (format nil "~A" key))

(defun xcb-delete-font (root-window font)
  "Forget FONT's xcb-truetype font.  Such fonts live entirely in Lisp, so
there is nothing to free on the server; this only drops the cache entries
that refer to it."
  (declare (ignore root-window))
  (let ((tt-font (and (schema-p font) (kr:g-cached-value font :xfont))))
    (when tt-font
      (maphash (lambda (key value)
                 (when (eq value tt-font)
                   (remhash key *xcb-font-cache-table*)))
               *xcb-font-cache-table*)))
  t)

(defun xcb-font-max-min-width (root-window font min-too)
  (let* ((tt-font (xcb-resolve-font root-window font))
         (target (or *default-xcb-screen* 96))
         (max-w (xcb-truetype:text-width target tt-font "M"))
         (min-w (xcb-truetype:text-width target tt-font "i")))
    (if min-too
        (values max-w min-w)
        max-w)))

(defun xcb-max-character-ascent (root-window font)
  (let* ((tt-font (xcb-resolve-font root-window font))
         (target (or *default-xcb-screen* 96)))
    (xcb-truetype:font-ascent target tt-font)))

(defun xcb-max-character-descent (root-window font)
  (let* ((tt-font (xcb-resolve-font root-window font))
         (target (or *default-xcb-screen* 96)))
    (abs (xcb-truetype:font-descent target tt-font))))

(defun xcb-character-width (root-window font character)
  (let* ((tt-font (xcb-resolve-font root-window font))
         (target (or *default-xcb-screen* 96))
         (str (if character (string (code-char character)) "X")))
    (xcb-truetype:text-width target tt-font str)))

(defun xcb-text-width (root-window opal-font string)
  (let* ((tt-font (xcb-resolve-font root-window opal-font))
         (target (or *default-xcb-screen* 96)))
    (xcb-truetype:text-width target tt-font (or string ""))))

(defun xcb-text-extents (root-window opal-font string)
  (let* ((tt-font (xcb-resolve-font root-window opal-font))
         (target (or *default-xcb-screen* 96))
         (str (or string ""))
         (width (xcb-truetype:text-width target tt-font str))
         (ascent (xcb-truetype:font-ascent target tt-font))
         (descent (abs (xcb-truetype:font-descent target tt-font))))
    (values width ascent descent 0 width width)))

(defun xcb-color-to-rgb-int (color)
  "Convert an Opal color schema or pixel to a 24-bit #x00RRGGBB integer."
  (if (and color (schema-p color))
      (let ((r (round (* (or (g-value color :red)   0.0) 255)))
            (g (round (* (or (g-value color :green) 0.0) 255)))
            (b (round (* (or (g-value color :blue)  0.0) 255))))
        (logior (ash r 16) (ash g 8) b))
      0))

(defun xcb-color-for-style (line-style invert-p)
  (if invert-p
      #xFFFFFF
      (if (and line-style (schema-p line-style))
          (let ((fg (g-value line-style :foreground-color)))
            (if fg
                (xcb-color-to-rgb-int fg)
                0))
          0)))

(defun xcb-get-xft-drawable (conn screen drawable-xid)
  (or (gethash drawable-xid *drawable-xft-table*)
      (setf (gethash drawable-xid *drawable-xft-table*)
            (make-instance (if (gethash drawable-xid *pixmap-table*)
                               'xcb-truetype:pixmap
                               'xcb-truetype:window)
                           :connection conn
                           :id drawable-xid
                           :screen screen))))

;;; An xcb-truetype drawable owns a RENDER picture once text has been drawn on
;;; it, and has a finalizer that frees the picture and the drawable itself.  So
;;; its entry must never simply be dropped from *DRAWABLE-XFT-TABLE*: the
;;; finalizer would later free XIDs that are already gone.  Either destroy it
;;; through XCB-TRUETYPE:DESTROY-DRAWABLE, or cancel its finalizer.

(defun xcb-release-drawable (conn xid raw-destroy-fn)
  "Destroy the window or pixmap XID.  If text was drawn on it, destroy it
through xcb-truetype, which also frees its RENDER picture; a pixmap's memory
is not released while a picture still refers to it.  Otherwise call
RAW-DESTROY-FN with CONN and XID."
  (let ((d (gethash xid *drawable-xft-table*)))
    (cond (d
           (remhash xid *drawable-xft-table*)
           (xcb-truetype:destroy-drawable d))
          (t
           (funcall raw-destroy-fn conn xid)))))

(defun xcb-forget-destroyed-drawable (xid)
  "Drop the xcb-truetype drawable for the window XID, which the server has
already destroyed together with its pictures, without sending anything."
  (let ((d (gethash xid *drawable-xft-table*)))
    (when d
      (remhash xid *drawable-xft-table*)
      (trivial-garbage:cancel-finalization d))))

(defun xcb-draw-text (window x y string font function
                      line-style &optional fill-background invert-p)
  (declare (ignore function))
  (let* ((display-info (g-value window :display-info))
         (conn (display-info-display display-info))
         (screen (display-info-screen display-info))
         (drawable (the-drawable window))
         (str (string string))
         (tt-font (xcb-resolve-font window font)))
    (when (and conn drawable tt-font (> (length str) 0))
      (let* ((xft-win (xcb-get-xft-drawable conn screen drawable))
             (fg (xcb-color-for-style line-style invert-p))
             (ascent (xcb-truetype:font-ascent screen tt-font)))
        (when fill-background
          (let* ((w (xcb-truetype:text-width screen tt-font str))
                 (h (+ ascent (abs (xcb-truetype:font-descent screen tt-font))))
                 (bg-top (- y ascent))
                 (bg-gc (display-info-filling-style-gc display-info))
                 (bg-color (if invert-p
                               (if (and line-style (schema-p line-style))
                                   (or (g-value line-style :foreground-color :colormap-index) *black*)
                                   *black*)
                               (if (and line-style (schema-p line-style))
                                   (or (g-value line-style :background-color :colormap-index) *white*)
                                   *white*))))
            (with-xcb-gc-changes (stage conn bg-gc)
              (stage :function +gx-copy+)
              (stage :foreground bg-color))
            (xcb:poly-fill-rectangle conn drawable (gem-gc-gcontext bg-gc)
                                     (list (make-instance 'xcb:rectangle
                                                          :x x :y bg-top
                                                          :width (max 1 w)
                                                          :height (max 1 h))))))
        (xcb-truetype:draw-text xft-win tt-font str x y :colour fg)))))


;;; Images and Pixmaps

(defun pixarray-element-type (depth)
  (cond
    ((= depth 1) 'bit)
    ((<= depth 8) '(unsigned-byte 8))
    ((<= depth 16) '(unsigned-byte 16))
    (t '(unsigned-byte 32))))

;;; Images are kept with rows padded only to a byte boundary, as .xbm files
;;; and the stipple patterns are, and as XCB-IMAGE-BIT and XCB-WRITE-AN-IMAGE
;;; expect.  PutImage wants each row padded to the server's scanline pad, so
;;; the rows are repacked just before upload.

(defun xcb-scanline-pad (conn depth)
  "Bits the server pads each PutImage row to for an image of DEPTH: the
bitmap format's pad for depth 1 (sent as XYBitmap), otherwise the pad of
the pixmap format for DEPTH."
  (if (= depth 1)
      (xcb:conn-bitmap-format-scanline-pad conn)
      (let ((format (find depth (xcb:conn-pixmap-formats conn) :key #'xcb:depth)))
        (if format (slot-value format 'xcb::scanline-pad) 32))))

(defun xcb-pad-image-rows (conn data height depth)
  "Return octet array DATA, holding HEIGHT rows of equal length, with each row
padded to CONN's scanline pad for DEPTH.  Returns DATA itself when its rows
are already padded, or when it is not an octet array of whole rows."
  (let ((total (array-total-size data)))
    (if (or (not (plusp height))
            (not (equal (array-element-type data) '(unsigned-byte 8)))
            (/= 0 (mod total height)))
        data
        (let* ((src-bpl (floor total height))
               (pad (floor (xcb-scanline-pad conn depth) 8))
               (dst-bpl (* pad (ceiling src-bpl pad))))
          (if (= src-bpl dst-bpl)
              data
              (let ((src (if (= (array-rank data) 1)
                             data
                             (make-array total :element-type '(unsigned-byte 8)
                                               :displaced-to data)))
                    (dst (make-array (* dst-bpl height)
                                     :element-type '(unsigned-byte 8)
                                     :initial-element 0)))
                (dotimes (y height dst)
                  (replace dst src :start1 (* y dst-bpl)
                                   :start2 (* y src-bpl)
                                   :end2 (* (1+ y) src-bpl)))))))))

(defun xcb-create-pixmap (root-window width height depth
                          &optional image bitmap-p data-array)
  (declare (ignore data-array))
  (let* ((conn (connection-for-window root-window))
         (screen (or (and root-window (schema-p root-window)
                          (let ((dinfo (g-value root-window :display-info)))
                            (and dinfo (display-info-screen dinfo))))
                     *default-xcb-screen*))
         (root (if screen (xcb:root screen) *default-xcb-root*))
         (pid (xcb:generate-id conn)))
    (xcb:create-pixmap conn depth pid root (max 1 width) (max 1 height))
    (setf (gethash pid *pixmap-table*) (list (max 1 width) (max 1 height) depth))
    (when image
      (let ((data (if (xcb-image-p image)
                      (xcb-image-data image)
                      image)))
        (when (arrayp data)
          (let ((tmp-gc (xcb:generate-id conn))
                (img-depth (cond ((xcb-image-p image)
                                  (xcb-image-depth image))
                                 (bitmap-p 1)
                                 (t depth))))
            (xcb:create-gc conn tmp-gc pid
                           (logior +gc-function+ +gc-foreground+ +gc-background+)
                           :function +gx-copy+
                           :foreground 1
                           :background 0)
            (xcb:put-image-chunked conn (if (= img-depth 1)
                                            +image-format-xy-bitmap+
                                            +image-format-z-pixmap+)
                                   pid tmp-gc
                                   width height 0 0 0 img-depth
                                   (xcb-pad-image-rows conn data height img-depth))
            (xcb:free-gc conn tmp-gc)))))
    pid))

(defun xcb-delete-pixmap (root-window pixmap &optional buffer-too)
  "Free PIXMAP.  With BUFFER-TOO, ROOT-WINDOW is the window PIXMAP is the
double buffer of, and its buffer GC is freed as well."
  (let ((conn (connection-for-window root-window)))
    (when (and conn pixmap)
      (remhash pixmap *pixmap-table*)
      (xcb-release-drawable conn pixmap #'xcb:free-pixmap))
    (when buffer-too
      (let ((buffer-gc (g-value root-window :buffer-gcontext)))
        (when (and conn buffer-gc)
          (xcb:free-gc conn (gem-gc-gcontext buffer-gc))
          (s-value root-window :buffer-gcontext nil))))))

(defun xcb-build-pixmap (window image width height bitmap-p)
  (xcb-create-pixmap window width height 1 image bitmap-p))

(defun xcb-copy-to-pixmap (root-window to from width height)
  (let* ((conn (connection-for-window root-window))
         (data (if (xcb-image-p from) (xcb-image-data from) from)))
    (when (and conn to (arrayp data))
      (let* ((tmp-gc (xcb:generate-id conn))
             (img-depth (if (xcb-image-p from) (xcb-image-depth from) 1)))
        (xcb:create-gc conn tmp-gc to
                       (logior +gc-function+ +gc-foreground+ +gc-background+)
                       :function +gx-copy+
                       :foreground *white*
                       :background *black*)
        (xcb:put-image-chunked conn (if (= img-depth 1)
                                        +image-format-xy-bitmap+
                                        +image-format-z-pixmap+)
                               to tmp-gc
                               width height 0 0 0 img-depth
                               (xcb-pad-image-rows conn data height img-depth))
        (xcb:free-gc conn tmp-gc)))))

(defun xcb-create-image (root-window width height depth from-data-p
                         &optional color-or-data properties
                           bits-per-pixel left-pad data-array)
  (declare (ignore root-window left-pad data-array))
  (let* ((bpp (or bits-per-pixel (depth-to-bits-per-pixel depth)))
         (bytes-per-line (ceiling (* width bpp) 8))
         (data (if from-data-p
                   color-or-data
                   (make-array (list height width)
                               :element-type (pixarray-element-type bpp)
                               :initial-element
                               (if (numberp color-or-data)
                                   color-or-data
                                   (if color-or-data
                                       (g-value color-or-data :colormap-index)
                                       *white*))))))
    (make-xcb-image :width width
                    :height height
                    :depth depth
                    :bits-per-pixel bpp
                    :bytes-per-line bytes-per-line
                    :data data
                    :properties properties
                    :x-hot (getf properties :x-hot 0)
                    :y-hot (getf properties :y-hot 0))))

(defun xcb-create-image-array (root-window width height depth)
  (declare (ignore root-window))
  (make-array (list height width)
              :element-type (pixarray-element-type depth)))

(defun xcb-image-size (a-window image)
  (declare (ignore a-window))
  (if (xcb-image-p image)
      (values (xcb-image-width image)
              (xcb-image-height image)
              (xcb-image-depth image))
      (values 16 16 1)))

(defun xcb-image-bit (root-window image x y)
  (declare (ignore root-window))
  (if (xcb-image-p image)
      (let* ((bytes-per-line (xcb-image-bytes-per-line image))
             (byte-pos (+ (floor x 8) (* bytes-per-line y)))
             (data (xcb-image-data image)))
        (if (and data (< byte-pos (array-total-size data)))
            (let ((byte (row-major-aref data byte-pos))
                  (bit-pos (mod x 8)))
              (logbitp bit-pos byte))
            nil))
      nil))

(defun xcb-image-to-array (root-window image)
  (declare (ignore root-window))
  (if (xcb-image-p image)
      (xcb-image-data image)
      image))

(defun xcb-image-hot-spot (root-window image)
  (declare (ignore root-window))
  (if (xcb-image-p image)
      (values (xcb-image-x-hot image)
              (xcb-image-y-hot image))
      (values 0 0)))

(defun xcb-get-descriptor (index)
  "Standard Garnet 4x4 halftone bit pattern descriptors for indices 0 to 16."
  (case index
    (0  '(#*0000 #*0000 #*0000 #*0000))
    (1  '(#*1000 #*0000 #*0000 #*0000))
    (2  '(#*1000 #*0000 #*0010 #*0000))
    (3  '(#*1010 #*0000 #*0010 #*0000))
    (4  '(#*1010 #*0000 #*1010 #*0000))
    (5  '(#*1010 #*0100 #*1010 #*0000))
    (6  '(#*1010 #*0100 #*1010 #*0001))
    (7  '(#*1010 #*0101 #*1010 #*0001))
    (8  '(#*1010 #*0101 #*1010 #*0101))
    (9  '(#*1010 #*0101 #*1010 #*0101))
    (10 '(#*1010 #*1101 #*1010 #*0101))
    (11 '(#*1010 #*1101 #*1010 #*1111))
    (12 '(#*1010 #*1111 #*1010 #*1111))
    (13 '(#*1010 #*1111 #*1011 #*1111))
    (14 '(#*1110 #*1111 #*1011 #*1111))
    (15 '(#*1110 #*1111 #*1111 #*1111))
    (16 '(#*1111 #*1111 #*1111 #*1111))
    (t  '(#*1111 #*1111 #*1111 #*1111))))

(defun xcb-image-from-bit-vectors (bitvecs)
  "Create a 16x16 1-bit XCB-IMAGE by tiling 4x4 bit vectors."
  (let ((arr (make-array 32 :element-type '(unsigned-byte 8)))
        (rows (coerce bitvecs 'simple-vector)))
    (dotimes (y 16)
      (let* ((bv (svref rows (mod y 4)))
             (n (logior (aref bv 0)
                        (ash (aref bv 1) 1)
                        (ash (aref bv 2) 2)
                        (ash (aref bv 3) 3)))
             (byte (logior n (ash n 4))))
        (setf (aref arr (* y 2)) byte)
        (setf (aref arr (1+ (* y 2))) byte)))
    (make-xcb-image :width 16
                    :height 16
                    :depth 1
                    :bits-per-pixel 1
                    :bytes-per-line 2
                    :data arr)))

(defun xcb-device-image (root-window index)
  (declare (ignore root-window))
  (let ((desc (xcb-get-descriptor index)))
    (xcb-image-from-bit-vectors desc)))

(defun xcb-image-from-bits (root-window patterns)
  (declare (ignore root-window))
  (cond
    ((null patterns) nil)
    ((bit-vector-p (first patterns))
     (xcb-image-from-bit-vectors patterns))
    (t
     (let* ((h (length patterns))
            (w 16)
            (arr (make-array (* h 2) :element-type '(unsigned-byte 8))))
       (loop for p in patterns
             for i from 0
             do (setf (aref arr (* i 2)) (logand p #xff))
                (setf (aref arr (1+ (* i 2))) (ash (logand p #xff00) -8)))
       (make-xcb-image :width w
                       :height h
                       :depth 1
                       :bits-per-pixel 1
                       :bytes-per-line 2
                       :data arr)))))

(defun xcb-draw-image (window left top width height image function fill-style)
  (let* ((display-info (g-value window :display-info))
         (conn (display-info-display display-info))
         (root-window (display-info-root-window display-info))
         (drawable (the-drawable window))
         (depth (if (xcb-image-p image)
                    (xcb-image-depth image)
                    1))
         (data (if (xcb-image-p image)
                   (xcb-image-data image)
                   image)))
    (when (and conn drawable fill-style (arrayp data))
      (let* ((gem-gc (display-info-filling-style-gc display-info))
             (gc-xid (gem-gc-gcontext gem-gc)))
        (set-xcb-filling-style conn fill-style gem-gc root-window function)
        (xcb:put-image-chunked conn (if (= depth 1)
                                        +image-format-xy-bitmap+
                                        +image-format-z-pixmap+)
                               drawable gc-xid
                               width height left top 0 depth
                               (xcb-pad-image-rows conn data height depth))))))

(defun xcb-window-to-image (window left top width height)
  "Create an XCB-IMAGE from a region of a window."
  (let* ((conn (the-display window))
         (drawable (the-drawable window)))
    (when (and conn drawable)
      (let* ((w (max 1 (round (or width (g-value window :width) 1))))
             (h (max 1 (round (or height (g-value window :height) 1))))
             (x (round (or left 0)))
             (y (round (or top 0)))
             (cookie (xcb:get-image conn +image-format-z-pixmap+ drawable x y w h #xffffffff))
             (reply (xcb:get-image-reply conn cookie)))
        (when reply
          (let* ((depth (xcb:depth reply))
                 (bpp (depth-to-bits-per-pixel depth))
                 (bytes-per-line (ceiling (* w bpp) 8))
                 (raw-data (xcb:data reply))
                 (arr (make-array (length raw-data)
                                  :element-type '(unsigned-byte 8)
                                  :initial-contents raw-data)))
            (make-xcb-image :width w
                            :height h
                            :depth depth
                            :bits-per-pixel bpp
                            :bytes-per-line bytes-per-line
                            :data arr)))))))

(defun xcb-stippled-p (root-window)
  "Return T if the filling style of the given display is stippled."
  (let* ((display-info (if (and root-window (schema-p root-window))
                           (or (g-value root-window :display-info) *display-info*)
                           *display-info*))
         (filling-gc (and display-info (display-info-filling-style-gc display-info))))
    (and filling-gc (eql (gem-gc-fill-style filling-gc) +fill-style-stippled+))))

(defun xcb-read-an-image (root-window pathname)
  "Read an X11 bitmap (.xbm) file from PATHNAME and return an XCB-IMAGE."
  (declare (ignore root-window))
  (with-open-file (stream pathname :direction :input :if-does-not-exist nil)
    (unless stream
      (return-from xcb-read-an-image nil))
    (let (width height x-hot y-hot (bytes nil))
      (loop for line = (read-line stream nil nil)
            while line do
              (cond
                ((search "_width" line)
                 (let ((parts (uiop:split-string line :separator " \t")))
                   (setf width (parse-integer (car (last parts)) :junk-allowed t))))
                ((search "_height" line)
                 (let ((parts (uiop:split-string line :separator " \t")))
                   (setf height (parse-integer (car (last parts)) :junk-allowed t))))
                ((search "_x_hot" line)
                 (let ((parts (uiop:split-string line :separator " \t")))
                   (setf x-hot (parse-integer (car (last parts)) :junk-allowed t))))
                ((search "_y_hot" line)
                 (let ((parts (uiop:split-string line :separator " \t")))
                   (setf y-hot (parse-integer (car (last parts)) :junk-allowed t))))
                ((search "static" line)
                 (let ((in-data t))
                   (loop while in-data
                         for l = (or line (read-line stream nil nil))
                         while l do
                           (let ((tokens (uiop:split-string l :separator " \t,{};")))
                             (dolist (tok tokens)
                               (when (and (> (length tok) 2)
                                          (string-equal (subseq tok 0 2) "0x"))
                                 (push (or (parse-integer (subseq tok 2) :radix 16 :junk-allowed t) 0)
                                       bytes))))
                           (when (search "}" l)
                             (setf in-data nil))
                           (setf line nil))))))
      (when (and width height bytes)
        (let* ((data-list (nreverse bytes))
               (bpp 1)
               (bpl (ceiling width 8))
               (arr (make-array (length data-list)
                                :element-type '(unsigned-byte 8)
                                :initial-contents data-list)))
          (make-xcb-image :width width
                          :height height
                          :depth 1
                          :bits-per-pixel bpp
                          :bytes-per-line bpl
                          :data arr
                          :x-hot x-hot
                          :y-hot y-hot))))))

(defun xcb-write-an-image (root-window pathname image)
  "Write an XCB-IMAGE to PATHNAME in standard X11 bitmap (.xbm) format."
  (declare (ignore root-window))
  (when (xcb-image-p image)
    (with-open-file (stream pathname :direction :output :if-exists :supersede :if-does-not-exist :create)
      (let* ((w (xcb-image-width image))
             (h (xcb-image-height image))
             (name (pathname-name pathname))
             (data (xcb-image-data image)))
        (format stream "#define ~A_width ~D~%" name w)
        (format stream "#define ~A_height ~D~%" name h)
        (when (xcb-image-x-hot image)
          (format stream "#define ~A_x_hot ~D~%" name (xcb-image-x-hot image)))
        (when (xcb-image-y-hot image)
          (format stream "#define ~A_y_hot ~D~%" name (xcb-image-y-hot image)))
        (format stream "static unsigned char ~A_bits[] = {~%" name)
        (let ((total (array-total-size data)))
          (dotimes (i total)
            (format stream " 0x~2,'0X~:[~;,~]~:[~;~%~]"
                    (row-major-aref data i)
                    (< i (1- total))
                    (zerop (mod (1+ i) 12)))))
        (format stream "};~%"))
      t)))


;;; Events, Keyboard Mapping, Cut Buffer & Interactors

(defvar *xcb-keyboard-mapping* nil
  "Cached vector of keysyms for keyboard mapping.")

(defvar *xcb-min-keycode* 8
  "Minimum keycode supported by X server.")

(defvar *xcb-keysyms-per-keycode* 2
  "Number of keysyms per keycode in the keyboard mapping.")

(defun init-xcb-keyboard-mapping (conn)
  "Query the X server for keyboard mapping and cache it."
  (when (and conn (open-stream-p (xcb:conn-stream conn)))
    (handler-case
        (let* ((min-kc (xcb:conn-min-keycode conn))
               (max-kc (xcb:conn-max-keycode conn))
               (count (1+ (- max-kc min-kc)))
               (cookie (xcb:get-keyboard-mapping conn min-kc count))
               (reply (xcb:get-keyboard-mapping-reply conn cookie)))
          (setf *xcb-min-keycode* min-kc
                *xcb-keysyms-per-keycode* (slot-value reply 'xcb:keysyms-per-keycode)
                *xcb-keyboard-mapping* (slot-value reply 'xcb:keysyms)))
      (cl:error () nil))))

(defun xcb-translate-code (window scan-code shiftp)
  "Translates a keyboard scan-code and shift status into a keysym."
  (declare (ignore window))
  (if (and *xcb-keyboard-mapping*
           (>= scan-code *xcb-min-keycode*))
      (let* ((base (* (- scan-code *xcb-min-keycode*) *xcb-keysyms-per-keycode*))
             (col (if shiftp 1 0))
             (idx (+ base col))
             (sym (if (< idx (length *xcb-keyboard-mapping*))
                      (aref *xcb-keyboard-mapping* idx)
                      0)))
        (if (zerop sym)
            (if (< base (length *xcb-keyboard-mapping*))
                (aref *xcb-keyboard-mapping* base)
                0)
            sym))
      0))

(defparameter *last-state* nil)
(defparameter *last-code* nil)
(declaim (integer *last-time*))
(defparameter *last-time* 0)
(defparameter *last-button-press* nil)

(defun xcb-check-double-press (root-window state code time)
  (declare (ignore root-window))
  (declare (integer time))
  (if inter::*double-click-time*
      (let (newcode)
        (if (and (eq state *last-state*)
                 (eq code *last-code*)
                 (<= (- time *last-time*) inter::*double-click-time*))
            (setf newcode (+ code inter::*double-offset*))
            (setf newcode code))
        (setf *last-state* state)
        (setf *last-code* code)
        (setf *last-time* time)
        newcode)
      code))

(defun xcb-set-interest-in-moved (window interestedp)
  #+garnet-debug
  (if (and inter::*int-debug* (inter::trace-test :mouse))
      (let ((*print-pretty* nil))
        (format t "interested in mouse moved now ~s~%" interestedp)))
  (let ((drawable (g-value window :drawable)))
    (if drawable
        (if interestedp
            (let* ((want-enter-leave (g-value window :want-enter-leave-events))
                   (em (if want-enter-leave :E-K-M :K-M)))
              (gem:mouse-grab window t want-enter-leave :CHANGE)
              (gem:set-window-property window :EVENT-MASK em)
              (s-value window :event-mask em))
            (let ((em (or (g-value window :ignore-motion-em)
                          (if (g-value window :want-enter-leave-events)
                              :E-K
                              :K))))
              (gem:set-window-property window :EVENT-MASK em)
              (s-value window :event-mask em)))
        (s-value window :want-running-em interestedp))))

(defun xcb-translate-mouse-character (root-window button-code modifier-bits event-key)
  (declare (ignore root-window))
  (case event-key
    (:button-release
     (aref inter::*mouse-up-translations* button-code
           (inter::modifier-index modifier-bits)))
    (:button-press
     (aref inter::*mouse-down-translations* button-code
           (inter::modifier-index modifier-bits)))))

(defun xcb-translate-character (window x y bits scan-code time)
  "Translates scan-code and modifier bits to a Lisp character."
  (declare (ignore x y time))
  (let (shiftp)
    (dolist (ele inter::*modifier-translations*)
      (unless (zerop (logand (car ele) bits))
        (case (cdr ele)
          (:shift (setf shiftp t))
          (:lock (setf shiftp t)))))
    (let* ((keysym (gem:translate-code window scan-code shiftp))
           (temp-char (gethash keysym inter::*keysym-translations*)))
      (if (null temp-char)
          (if (<= xcb-const:+xk-shift-l+ keysym xcb-const:+xk-hyper-r+) ; modifier keys
              nil
              (unless inter::*ignore-undefined-keys*
                (error "Undefined keysym ~S, describe Inter:DEFINE-KEYSYM."
                       keysym)))
          (inter::base-char-to-character temp-char bits)))))

(defun xcb-create-cursor (root-window source mask foreground background from-font-p x y)
  (let* ((conn (the-display (or root-window (g-value gem:device-info :current-root))))
         (cid (and conn (xcb:generate-id conn))))
    (when (and conn cid)
      (multiple-value-bind (fore-r fore-g fore-b)
          (cond
            ((and (consp foreground) (= (length foreground) 3))
             (values (first foreground) (second foreground) (third foreground)))
            ((and (kr:schema-p foreground) (g-value foreground :red))
             (values (round (* #xffff (g-value foreground :red)))
                     (round (* #xffff (g-value foreground :green)))
                     (round (* #xffff (g-value foreground :blue)))))
            (t (values 0 0 0)))
        (multiple-value-bind (back-r back-g back-b)
            (cond
              ((and (consp background) (= (length background) 3))
               (values (first background) (second background) (third background)))
              ((and (kr:schema-p background) (g-value background :red))
               (values (round (* #xffff (g-value background :red)))
                       (round (* #xffff (g-value background :green)))
                       (round (* #xffff (g-value background :blue)))))
              (t (values #xffff #xffff #xffff)))
          (if from-font-p
              (let* ((src-font (if (numberp source)
                                   source
                                   (or (and (kr:schema-p source)
                                            (g-value source :xfont))
                                       (xcb-font-to-internal root-window source))))
                     (msk-font (if (numberp mask)
                                   mask
                                   (or (and (kr:schema-p mask)
                                            (g-value mask :xfont))
                                       src-font))))
                (xcb:create-glyph-cursor conn cid src-font msk-font
                                         (or x 0) (or y 0)
                                         fore-r fore-g fore-b
                                         back-r back-g back-b))
              (let ((src-pm (if (numberp source)
                                source
                                (and (kr:schema-p source)
                                     (g-value source :pixmap))))
                    (msk-pm (if (numberp mask)
                                mask
                                (or (and (kr:schema-p mask)
                                         (g-value mask :pixmap))
                                    +pixmap-none+))))
                (xcb:create-cursor conn cid
                                   (or src-pm +pixmap-none+)
                                   (or msk-pm +pixmap-none+)
                                   fore-r fore-g fore-b
                                   back-r back-g back-b
                                   (or x 0) (or y 0))))
          cid)))))

(defun xcb-create-state-mask (root-window modifier)
  (if (listp modifier)
      (reduce #'logior
              (mapcar (lambda (m)
                        (xcb-create-state-mask root-window m))
                      modifier)
              :initial-value 0)
      (case modifier
        (:shift +mod-mask-shift+)
        (:lock +mod-mask-lock+)
        (:control +mod-mask-control+)
        (:mod-1 +mod-mask-n1+)
        (:mod-2 +mod-mask-n2+)
        (:mod-3 +mod-mask-n3+)
        (:mod-4 +mod-mask-n4+)
        (:mod-5 +mod-mask-n5+)
        (:button-1 +key-but-mask-button1+)
        (:button-2 +key-but-mask-button2+)
        (:button-3 +key-but-mask-button3+)
        (:button-4 +key-but-mask-button4+)
        (:button-5 +key-but-mask-button5+)
        (t (if (numberp modifier) modifier 0)))))

(defun xcb-get-cut-buffer (root-window)
  "Retrieve text from root window property XA_CUT_BUFFER0."
  (let* ((conn (the-display (or root-window (g-value gem:device-info :current-root))))
         (root (and conn (xcb:root (display-info-screen *display-info*)))))
    (if (and conn root)
        (handler-case
            (let* ((cookie (xcb:get-property conn 0 root +atom-cut-buffer0+ +atom-string+ 0 65536))
                   (reply (xcb:get-property-reply conn cookie)))
              (if (and reply (> (slot-value reply 'xcb:value-len) 0))
                  (let ((val (slot-value reply 'xcb:value)))
                    (if (typep val 'sequence)
                        (map 'string #'code-char val)
                        ""))
                  ""))
          (cl:error () ""))
        "")))

(defun xcb-set-cut-buffer (root-window string)
  "Store string into root window property XA_CUT_BUFFER0."
  (let* ((conn (the-display (or root-window (g-value gem:device-info :current-root))))
         (root (and conn (xcb:root (display-info-screen *display-info*)))))
    (when (and conn root (stringp string))
      (handler-case
          (xcb:send-change-property conn +prop-mode-replace+ root
                                    +atom-cut-buffer0+ +atom-string+ 8 string)
        (cl:error () nil))))
  nil)

(defun xcb-drain-socket (conn)
  "Read every packet already available on CONN without blocking: queue the
events, retain the replies and signal the errors.  XCB:POLL-FOR-EVENT pops a
queued event and stops reading as soon as one event is queued, so pop events
until it returns NIL, then put them back in order."
  (let ((events '()))
    (unwind-protect
         (loop for ev = (xcb:poll-for-event conn)
               while ev
               do (push ev events))
      ;; Also on a protocol error, so events read before it are not lost.
      (setf (xcb:conn-event-queue conn)
            (nconc (nreverse events) (xcb:conn-event-queue conn))))))

(defun xcb-discard-mouse-moved-events (root-window)
  (let* ((conn (the-display root-window))
         (current-x nil)
         (current-y nil)
         (current-win nil))
    (when conn
      (xcb-drain-socket conn)
      (loop while (and (xcb:conn-event-queue conn)
                       (typep (first (xcb:conn-event-queue conn)) 'xcb:motion-notify))
            do (let ((ev (pop (xcb:conn-event-queue conn))))
                 (setf current-x (slot-value ev 'xcb:event-x)
                       current-y (slot-value ev 'xcb:event-y)
                       current-win (slot-value ev 'xcb:event)))))
    (values current-x current-y
            (if current-win
                (xcb-window-from-drawable root-window current-win)
                nil))))

(defun xcb-discard-pending-events (root-window &optional (timeout 0))
  (let ((conn (the-display root-window)))
    (when conn
      (setf (xcb:conn-event-queue conn) nil)
      (when (and timeout (> timeout 0))
        (when (xcb:wait-for-x-event-or-timeout conn timeout)
          (xcb-drain-socket conn)
          (setf (xcb:conn-event-queue conn) nil)))
      (xcb-drain-socket conn)
      (setf (xcb:conn-event-queue conn) nil)))
  t)

(defun xcb-inject-event (window index)
  (let* ((drawable (g-value window :drawable))
         (conn (the-display window)))
    (when (and conn drawable)
      (let ((timer-atom (xcb:intern-atom-id conn "TIMER_EVENT")))
        (xcb:send-client-message conn drawable 0 drawable timer-atom (list index))))))

(defun xcb-event-handler (root-window ignore-keys)
  "Wait for and dispatch events from XCB connection to Garnet interactors."
  (let ((conn (the-display root-window)))
    (unless conn
      (return-from xcb-event-handler nil))
    (finish-output (xcb:conn-stream conn))
    (let ((ev (if ignore-keys
                  (xcb:poll-for-event conn)
                  (loop
                    (let ((e (xcb:poll-for-event conn)))
                      (when e (return e)))
                    ;; Block until the server sends something, as the CLX
                    ;; backend does (:TIMEOUT NIL).  The main loop is left
                    ;; through *EXIT-MAIN-EVENT-LOOP-FUNCTION*, which Opal
                    ;; calls while handling the unmap or destroy event.
                    (xcb:wait-for-x-event-or-timeout conn nil)
                    (when (and opal::*inside-main-event-loop*
                               (not (opal::any-top-level-window-visible)))
                      (return-from xcb-event-handler nil))))))
      (unless ev
        (return-from xcb-event-handler nil))
      (typecase ev
        (xcb:key-press
         (let ((event-win (slot-value ev 'xcb:event))
               (x (slot-value ev 'xcb:event-x))
               (y (slot-value ev 'xcb:event-y))
               (state (slot-value ev 'xcb:state))
               (code (slot-value ev 'xcb:detail))
               (time (slot-value ev 'xcb:time)))
           (if ignore-keys
               (let ((c (xcb-translate-character *root-window* 0 0 state code 0)))
                 (when (eq c interactors::*garnet-break-key*)
                   (format t "~%**Aborting transcript due to user command**~%")
                   (return-from xcb-event-handler :abort)))
               (let ((win (xcb-window-from-drawable root-window event-win)))
                 (when win
                   (interactors::do-key-press win x y state code time))))))
        (xcb:key-release
         t)
        (xcb:button-press
         (let ((event-win (slot-value ev 'xcb:event))
               (x (slot-value ev 'xcb:event-x))
               (y (slot-value ev 'xcb:event-y))
               (state (slot-value ev 'xcb:state))
               (code (slot-value ev 'xcb:detail))
               (time (slot-value ev 'xcb:time)))
           (setf *last-button-press* time)
           (unless ignore-keys
             (let ((win (xcb-window-from-drawable root-window event-win)))
               (when win
                 (interactors::do-button-press win x y state code time :button-press))))))
        (xcb:button-release
         (let ((event-win (slot-value ev 'xcb:event))
               (x (slot-value ev 'xcb:event-x))
               (y (slot-value ev 'xcb:event-y))
               (state (slot-value ev 'xcb:state))
               (code (slot-value ev 'xcb:detail))
               (time (slot-value ev 'xcb:time)))
           (unless ignore-keys
             (let ((win (xcb-window-from-drawable root-window event-win)))
               (when win
                 (interactors::do-button-release win x y state code time :button-release))))
           (setf *last-button-press* nil)))
        (xcb:motion-notify
         (let ((event-win (slot-value ev 'xcb:event))
               (x (slot-value ev 'xcb:event-x))
               (y (slot-value ev 'xcb:event-y)))
           (unless ignore-keys
             (let ((win (xcb-window-from-drawable root-window event-win)))
               (when win
                 (interactors::do-motion-notify win x y conn))))))
        (xcb:enter-notify
         (let ((event-win (slot-value ev 'xcb:event))
               (x (slot-value ev 'xcb:event-x))
               (y (slot-value ev 'xcb:event-y))
               (time (slot-value ev 'xcb:time)))
           (unless ignore-keys
             (let ((win (xcb-window-from-drawable root-window event-win)))
               (when win
                 (interactors::do-enter-notify win x y time))))))
        (xcb:leave-notify
         (let ((event-win (slot-value ev 'xcb:event))
               (x (slot-value ev 'xcb:event-x))
               (y (slot-value ev 'xcb:event-y))
               (time (slot-value ev 'xcb:time)))
           (unless ignore-keys
             (let ((win (xcb-window-from-drawable root-window event-win)))
               (when win
                 (interactors::do-leave-notify win x y time))))))
        (xcb:expose
         (let ((event-win (slot-value ev 'xcb:window))
               (x (slot-value ev 'xcb:x))
               (y (slot-value ev 'xcb:y))
               (width (slot-value ev 'xcb:width))
               (height (slot-value ev 'xcb:height))
               (count (slot-value ev 'xcb:count)))
           (when (xcb-connected-window-p event-win)
             (interactors::do-exposure (xcb-window-from-drawable root-window event-win)
                                       x y width height count conn))))
        (xcb:configure-notify
         (let ((event-win (slot-value ev 'xcb:window))
               (x (slot-value ev 'xcb:x))
               (y (slot-value ev 'xcb:y))
               (width (slot-value ev 'xcb:width))
               (height (slot-value ev 'xcb:height))
               (above-sibling (slot-value ev 'xcb:above-sibling)))
           (when (xcb-connected-window-p event-win)
             (interactors::do-configure-notify (xcb-window-from-drawable root-window event-win)
                                               x y width height above-sibling))))
        (xcb:map-notify
         (let ((event-win (slot-value ev 'xcb:window)))
           (interactors::do-map-notify (xcb-window-from-drawable root-window event-win))))
        (xcb:unmap-notify
         (let ((event-win (slot-value ev 'xcb:window)))
           (interactors::do-unmap-notify (xcb-window-from-drawable root-window event-win))))
        (xcb:client-message
         (let* ((event-win (slot-value ev 'xcb:window))
                (fmt (slot-value ev 'xcb:format))
                (msg-type (slot-value ev 'xcb:type))
                (raw-words (xcb::%client-message-data32 ev))
                (data32 (make-array 5 :element-type '(unsigned-byte 32)
                                      :initial-contents
                                      (loop for i from 0 below 5
                                            collect (if (and raw-words
                                                             (< i (length raw-words)))
                                                        (elt raw-words i)
                                                        0))))
                (timer-atom (xcb:intern-atom-id conn "TIMER_EVENT"))
                (effective-type (if (eql msg-type timer-atom) :TIMER_EVENT msg-type)))
           (interactors::do-client-message event-win effective-type data32 fmt conn)))
        (xcb:destroy-notify
         (let ((event-win (slot-value ev 'xcb:window)))
           (remhash event-win *drawable-to-window-table*)
           (xcb-forget-destroyed-drawable event-win)
           (finish-output (xcb:conn-stream conn))))
        (xcb:reparent-notify
         (let ((event-win (slot-value ev 'xcb:window)))
           (when (xcb-connected-window-p event-win)
             (let ((win (xcb-window-from-drawable root-window event-win)))
               (s-value win :already-initialized-border-widths nil)))))
        (xcb:circulate-notify
         (interactors::do-circulate-notify))
        (xcb:gravity-notify
         (interactors::do-gravity-notify))
        (t
         t))
      t)))


;;; Method Attachment Table

(defun attach-xcb-methods (xcb-device)
  (macrolet ((attach-xcb-devices (&body keys)
               ;; Each KEY expands to (attach-method xcb-device KEY #'xcb-KEY);
               ;; every attached method in this file is named XCB-<KEY>.  A KEY
               ;; with no such function shows up as an undefined-function
               ;; warning at the end of compiling this file.
               `(progn
                  ,@(loop for key in keys
                          for fn = (intern (format nil "XCB-~A" (symbol-name key)) '#:gem)
                          collect `(attach-method xcb-device ,key #',fn)))))
    (attach-xcb-devices
      ;; Device & window queries
      :all-garnet-windows
      :beep
      :black-white-pixel
      :color-to-index
      :colormap-property
      :query-color
      :drawable-to-window
      :window-from-drawable
      :drawable-equal
      :check-wm-delete-window
      :window-debug-id
      :window-depth
      :window-has-grown
      :flush-output
      :device-batch-changes

      ;; Window lifecycle & management
      :create-window
      :delete-window
      :map-and-wait
      :reparent
      :raise-or-lower
      :initialize-window-borders
      :set-window-property
      :translate-coordinates
      :mouse-grab
      :set-drawable-to-window
      :set-draw-function-alist
      :set-draw-functions

      ;; Drawing Primitives
      :clear-area
      :draw-rectangle
      :draw-line
      :draw-lines
      :draw-points
      :draw-arc
      :draw-roundtangle
      :draw-text
      :draw-image
      :bit-blit
      :set-clip-mask

      ;; Fonts and Text
      :font-exists-p
      :font-name-p
      :make-font-name
      :font-to-internal
      :delete-font
      :font-max-min-width
      :max-character-ascent
      :max-character-descent
      :character-width
      :text-width
      :text-extents

      ;; Pixmaps & Images
      :create-pixmap
      :delete-pixmap
      :build-pixmap
      :copy-to-pixmap
      :create-image
      :create-image-array
      :image-size
      :image-bit
      :image-to-array
      :image-hot-spot
      :image-from-bits
      :device-image
      :window-to-image
      :read-an-image
      :write-an-image
      :stippled-p

      ;; Events & Cut Buffer
      :create-cursor
      :create-state-mask
      :get-cut-buffer
      :set-cut-buffer
      :discard-mouse-moved-events
      :discard-pending-events
      :event-handler
      :inject-event
      :translate-code

      ;; Interactor methods from xcb-inter.lisp
      :check-double-press
      :set-interest-in-moved
      :translate-mouse-character
      :translate-character)

    ;; Inherit methods to Opal window prototype
    (set-window-methods opal::window xcb-device)))

;;; Register device backend with GEM, make it default, and initialize
(register-device :xcb #'init-xcb-device #'init-xcb-device-post)
(setf *default-device-type* :xcb)

(if *x11-server-available*
    (progn
      (init-xcb-device)
      (init-xcb-device-post))
    (warn "X11 server is not available; skipping XCB device initialization."))
