;;; -*- Mode: LISP; Syntax: Common-Lisp; Package: GEM; Base: 10 -*-
;;;
;;; Wayland Device Backend for GEM (Garnet Extension Mechanism)
;;;
;;; Implements the GEM device abstraction on a Wayland compositor through
;;; Wayflan (a pure Common Lisp Wayland client).
;;;
;;; Wayland differs from X11 in ways that shape this backend:
;;;
;;; * The compositor draws nothing.  Every window and pixmap is a
;;;   PX-SURFACE in Lisp memory, drawn on by the rasterizer in
;;;   wl-raster.lisp, which follows X11's rules.  A top-level window is
;;;   shown by copying it, with its subwindows, into a wl_shm buffer and
;;;   committing that.
;;;
;;; * Only top-level windows are Wayland surfaces (xdg_toplevel, or
;;;   xdg_popup for Opal's override-redirect windows: menus).  Subwindows
;;;   live on the client side; their pixels are composited into their
;;;   top-level window, and pointer events are routed to them here.
;;;
;;; * A client cannot know or set where its windows are on the screen.
;;;   Each top-level window keeps the position Opal gave it, as a virtual
;;;   screen position, so that TRANSLATE-COORDINATES and popup placement
;;;   agree with each other.
;;;
;;; * Text is drawn on the client too, by Runes: each glyph's alpha
;;;   map is blended into the drawable.
;;;
;;; * Keys arrive as evdev codes with an XKB keymap from the compositor,
;;;   which libxkbcommon (through cl-xkb) turns into keysyms: the same
;;;   numbers X11 keysyms are, so Garnet's key translation tables apply.
;;;   Keys repeat on the client side.
;;;

(in-package :gem)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (use-package '(:wayflan-client :wayflan-client.xdg-shell) :gem))


;;; Connection and Device State

(defvar *wl-display* nil "The Wayflan display Garnet is connected to.")
(defvar *wl-thread* nil
  "The thread that talks to the compositor: the one that connected, or last
ran the event handler.  A Wayflan display is not safe to use from two
threads.")

(defvar *wl-compositor* nil)
(defvar *wl-shm* nil)
(defvar *wl-wm-base* nil)
(defvar *wl-seat* nil)
(defvar *wl-pointer* nil)
(defvar *wl-keyboard* nil)
(defvar *wl-cursor-shape-manager* nil "wp_cursor_shape_manager_v1, if offered.")
(defvar *wl-cursor-shape-device* nil)
(defvar *wl-data-device-manager* nil "wl_data_device_manager, for the clipboard.")
(defvar *wl-data-device* nil)
(defvar *wl-viewporter* nil "wp_viewporter, to show buffers at logical size.")
(defvar *wl-fractional-scale-manager* nil "wp_fractional_scale_manager_v1.")

(defvar *wl-scale* 1
  "Device pixels per logical pixel, as the compositor prefers for Garnet's
windows: 1.25 on a display scaled to 125%.  Windows and their double
buffers are drawn at this scale; Opal works in logical pixels.")

(defvar *wl-root* nil
  "The WL-WINDOW standing for the screen: the parent of top-level windows.")

(defvar *wl-line-gc* nil)
(defvar *wl-fill-gc* nil)

(defvar *wl-dpi* 72
  "The DPI text is measured and drawn at.  At 72 a point is a pixel, so
Garnet's font sizes (:MEDIUM is 12) are pixel sizes, as they were with X
core fonts.")

(defparameter *wl-drawable-to-window-table* (make-hash-table :test 'eq)
  "Drawable (WL-WINDOW or PX-SURFACE) -> Opal window.")

(defparameter *wl-surface-to-window* (make-hash-table :test 'eq)
  "wl_surface proxy -> the top-level WL-WINDOW it shows.")

(defvar *display-info*
  (make-display-info :display nil :screen nil :root-window nil
                     :line-style-gc nil :filling-style-gc nil))

(defvar *copy* +px-gx-copy+)

;;; Device schema for Wayland
(create-schema 'wl-device (:root-window *root-window*) (:device-type :wl))

(defun get-full-display-name ()
  "The Wayland display's name, as $WAYLAND_DISPLAY gives it.  (The core
calls this only for the X device; the X backends define it too.)"
  (or (uiop:getenv "WAYLAND_DISPLAY") "wayland-0"))

;;; Events for Garnet, queued by the Wayland event hooks and by timer
;;; threads, and taken off by WL-EVENT-HANDLER.  Each is a list whose first
;;; element names the kind of event.

(defvar *wl-event-queue* '())
(defvar *wl-event-queue-tail* '())
(defvar *wl-event-lock* (bt:make-lock "garnet-wl events"))
(defvar *wl-wake-read-fd* nil)
(defvar *wl-wake-write-fd* nil)

(defun wl-queue-event (event)
  (bt:with-lock-held (*wl-event-lock*)
    (let ((cell (list event)))
      (if *wl-event-queue*
          (setf (cdr *wl-event-queue-tail*) cell)
          (setf *wl-event-queue* cell))
      (setf *wl-event-queue-tail* cell))))

(defun wl-pop-event ()
  (bt:with-lock-held (*wl-event-lock*)
    (pop *wl-event-queue*)))

(defun wl-clear-event-queue ()
  (bt:with-lock-held (*wl-event-lock*)
    (setf *wl-event-queue* nil)))


;;; Images: what Opal gets from CREATE-IMAGE and READ-AN-IMAGE.  A
;;; bitmap's DATA holds rows of BYTES-PER-LINE bytes, bits LSB first, as
;;; in .xbm files; a color image's is a (HEIGHT WIDTH) array of pixels.

(defstruct wl-image
  width height depth bits-per-pixel bytes-per-line data properties x-hot y-hot)

;;; Windows
;;;
;;; A WL-WINDOW is the drawable of an Opal window.  KIND is :ROOT, :TOPLEVEL,
;;; :POPUP or :CHILD.  X and Y are relative to the parent; for top-level
;;; windows, they are the virtual screen position.  CHILDREN are in
;;; stacking order, bottom first.

(defstruct (wl-window (:print-function
                       (lambda (w s d)
                         (declare (ignore d))
                         (format s "#<WL-WINDOW ~A ~Dx~D+~D+~D~:[~; mapped~]>"
                                 (wl-window-kind w) (wl-window-width w)
                                 (wl-window-height w) (wl-window-x w)
                                 (wl-window-y w) (wl-window-mapped w)))))
  (kind :child)
  parent
  (children '())
  (x 0) (y 0) (width 1) (height 1)
  (mapped nil)
  pixels                                ; PX-SURFACE
  (background #xFFFFFF)
  title
  (event-mask :default)
  (cursor nil)                          ; from WL-CREATE-CURSOR; NIL: the parent's
  override-redirect
  min-width min-height max-width max-height
  ;; Wayland objects, for a top-level window while it is mapped.
  wl-surface xdg-surface xdg-toplevel xdg-popup
  viewport fractional-scale
  (viewport-size nil)                   ; the destination last set
  (configured nil)
  ;; The wl_callback of the last commit's frame request, until the
  ;; compositor says it is time to draw the next frame.
  (frame-callback nil)
  (buffers '())                         ; WL-SHM-BUFFERs
  (damage nil))                         ; (X0 Y0 X1 Y1) not yet presented

(defstruct wl-shm-buffer
  proxy pointer fd size width height
  (busy nil)
  (stale nil))                          ; (X0 Y0 X1 Y1) out of date in it

(defun wl-top-level (win)
  "The top-level window (or root) WIN is in, and WIN's offset in it."
  (let ((x 0) (y 0))
    (loop while (eq (wl-window-kind win) :child)
          do (incf x (wl-window-x win))
             (incf y (wl-window-y win))
             (setf win (wl-window-parent win)))
    (values win x y)))

(defun wl-window-shown-p (win)
  "Whether WIN and all its ancestors up to its top-level window are mapped."
  (loop while (eq (wl-window-kind win) :child)
        do (unless (wl-window-mapped win) (return-from wl-window-shown-p nil))
           (setf win (wl-window-parent win)))
  (wl-window-mapped win))

(defun wl-screen-origin (win)
  "WIN's top left in virtual screen coordinates."
  (if (or (null win) (eq (wl-window-kind win) :root))
      (values 0 0)
      (multiple-value-bind (px py) (wl-screen-origin (wl-window-parent win))
        (values (+ px (wl-window-x win)) (+ py (wl-window-y win))))))

(defun rect-union (a b)
  (if a
      (list (min (first a) (first b)) (min (second a) (second b))
            (max (third a) (third b)) (max (fourth a) (fourth b)))
      b))

;;; Logical to device pixels.  A logical edge X becomes device edge
;;; (ROUND (* X K)), so areas that tile still tile; a logical pixel's
;;; centre, where X puts a vertex, becomes the centre of its device
;;; pixels, (X + 1/2) K - 1/2.

(declaim (inline dev-edge dev-centre))
(defun dev-edge (v k) (round (* v k)))
(defun dev-centre (v k) (- (* (+ v 1/2) k) 1/2))
(defun dev-centre-i (v k) (round (dev-centre v k)))

(defun dev-size (n k) (max 1 (round (* n k))))

(defun dev-rect (x y w h k)
  "The device rectangle (X Y W H) of the logical one."
  (let ((x0 (dev-edge x k)) (y0 (dev-edge y k)))
    (values x0 y0 (- (dev-edge (+ x w) k) x0) (- (dev-edge (+ y h) k) y0))))

(defun dev-line-width (lw k)
  "LW logical pixels wide, at scale K.  A line covers the device pixels of
the logical pixels it runs through, as fills do: X's zero-width lines are
one logical pixel wide, K device pixels -- 1 or 2 by turns at 1.25 -- so
that lines side by side tile, with no gaps between them nor overlaps."
  (if (= k 1)
      lw
      (* (max 1 lw) k)))

(defun wl-gc-device (gc k)
  "Make GC's clip, line width and dashes those of the logical ones at
scale K, for drawing on a surface of that scale."
  (setf (px-gc-line-width gc) (dev-line-width (px-gc-logical-line-width gc) k))
  (when (member (px-gc-line-style gc) '(:dash :double-dash))
    (setf (px-gc-dashes gc) (mapcar (lambda (d) (max 1 (round (* d k))))
                                    (px-gc-logical-dashes gc))))
  (let ((logical (px-gc-logical-clip gc)))
    (setf (px-gc-clip gc)
          (if (or (eq logical :none) (= k 1))
              logical
              (if (and (eq (px-gc-clip-scale gc) k) (not (eq (px-gc-clip gc) logical)))
                  (px-gc-clip gc)
                  (loop for (x y w h) in logical
                        collect (multiple-value-list (dev-rect x y w h k))))))
    (setf (px-gc-clip-scale gc) k))
  gc)

(defun wl-scale-of (drawable)
  (px-surface-scale (wl-target drawable)))

(defvar *wl-dirty-windows* '()
  "Top-level windows with damage not yet presented.")

(defun wl-damage (win x y w h)
  "Note that the logical rectangle (X Y W H) of WIN has changed.  Damage
is kept in the device pixels of the top-level window's buffer."
  (when (and (plusp w) (plusp h))
    (multiple-value-bind (top ox oy) (wl-top-level win)
      (unless (eq (wl-window-kind top) :root)
        (let* ((k (px-surface-scale (wl-window-pixels top)))
               (x0 (max 0 (dev-edge (+ x ox) k))) (y0 (max 0 (dev-edge (+ y oy) k)))
               (x1 (min (px-surface-width (wl-window-pixels top)) (dev-edge (+ x ox w) k)))
               (y1 (min (px-surface-height (wl-window-pixels top)) (dev-edge (+ y oy h) k))))
          (when (and (< x0 x1) (< y0 y1))
            (setf (wl-window-damage top)
                  (rect-union (wl-window-damage top) (list x0 y0 x1 y1)))
            (pushnew top *wl-dirty-windows*)))))))

(defun wl-damage-all (win)
  (wl-damage win 0 0 (wl-window-width win) (wl-window-height win)))

(defun wl-target (drawable)
  "The PX-SURFACE drawn on for DRAWABLE, a WL-WINDOW or a pixmap."
  (if (wl-window-p drawable) (wl-window-pixels drawable) drawable))

(defun wl-note-drawn (drawable x y w h)
  "After drawing on DRAWABLE within (X Y W H), damage it if it is a window."
  (when (wl-window-p drawable)
    (wl-damage drawable (floor x) (floor y) (ceiling w) (ceiling h))))


;;; Presentation: composite a top-level window and its subwindows into a
;;; wl_shm buffer, and commit it.

(defun wl-free-buffer (buffer)
  "Free BUFFER, now or, if the compositor still holds it, when it lets go."
  (if (wl-shm-buffer-busy buffer)
      (setf (wl-shm-buffer-busy buffer) :free-on-release)
      (progn
        (destroy-proxy (wl-shm-buffer-proxy buffer))
        (%wl-munmap (wl-shm-buffer-pointer buffer) (wl-shm-buffer-size buffer))
        (%wl-close (wl-shm-buffer-fd buffer)))))

(defun wl-make-buffer (width height)
  (let* ((stride (* 4 width))
         (size (* stride height)))
    (multiple-value-bind (fd ptr) (wl-make-shm size)
      (let* ((pool (wl-shm.create-pool *wl-shm* fd size))
             (proxy (wl-shm-pool.create-buffer pool 0 width height stride :xrgb8888))
             (buffer (make-wl-shm-buffer :proxy proxy :pointer ptr :fd fd :size size
                                         :width width :height height
                                         :stale (list 0 0 width height))))
        (destroy-proxy pool)
        (push (evelambda
                (:release ()
                 (if (eq (wl-shm-buffer-busy buffer) :free-on-release)
                     (progn (setf (wl-shm-buffer-busy buffer) nil)
                            (wl-free-buffer buffer))
                     (setf (wl-shm-buffer-busy buffer) nil))))
              (wl-proxy-hooks proxy))
        buffer))))

(defun wl-copy-rows (src sx sy dst-ptr dst-width x0 y0 x1 y1)
  "Copy the rectangle [X0,X1)x[Y0,Y1) of the destination, which is SRC's
pixels offset by (SX, SY), into the XRGB8888 buffer at DST-PTR."
  (let* ((sw (px-surface-width src))
         (sh (px-surface-height src))
         (ax (max x0 sx)) (bx (min x1 (+ sx sw)))
         (pixels (px-surface-pixels src)))
    (when (< ax bx)
      (cffi:with-pointer-to-vector-data (p pixels)
        (loop for y from (max y0 sy) below (min y1 (+ sy sh))
              do (%wl-memcpy (cffi:inc-pointer dst-ptr (* 4 (+ (* y dst-width) ax)))
                             (cffi:inc-pointer p (* 4 (+ (* (- y sy) sw) (- ax sx))))
                             (* 4 (- bx ax))))))))

(defun wl-composite (win lx ly buffer x0 y0 x1 y1)
  "Composite WIN, at logical (LX, LY) in BUFFER, and its mapped subwindows,
within the device rectangle [X0,X1)x[Y0,Y1)."
  (let* ((pixels (wl-window-pixels win))
         (k (px-surface-scale pixels))
         (ox (dev-edge lx k)) (oy (dev-edge ly k))
         (cx0 (max x0 ox)) (cy0 (max y0 oy))
         (cx1 (min x1 (+ ox (px-surface-width pixels))))
         (cy1 (min y1 (+ oy (px-surface-height pixels)))))
    (when (and (< cx0 cx1) (< cy0 cy1))
      (wl-copy-rows pixels ox oy (wl-shm-buffer-pointer buffer)
                    (wl-shm-buffer-width buffer) cx0 cy0 cx1 cy1)
      (dolist (child (wl-window-children win))
        (when (wl-window-mapped child)
          (wl-composite child (+ lx (wl-window-x child)) (+ ly (wl-window-y child))
                        buffer cx0 cy0 cx1 cy1))))))

(defun wl-request-frame (top surface)
  "Ask to be told when the compositor would show TOP's next frame.  Until
then, its damage only accumulates, so that drawing faster than the screen
refreshes commits no frames that would never be seen."
  (let ((callback (wl-surface.frame surface)))
    (setf (wl-window-frame-callback top) callback)
    (push (evlambda
            (:done (time)
             (declare (ignore time))
             ;; A late callback, from before TOP was hidden, is not ours.
             (when (eq (wl-window-frame-callback top) callback)
               (setf (wl-window-frame-callback top) nil)
               (when (wl-window-damage top)
                 (wl-present top)))))
          (wl-proxy-hooks callback))))

(defun wl-present (top)
  "Show TOP's damage, if it can be shown now: not while the frame last
committed is still waiting for the compositor."
  (let ((damage (wl-window-damage top))
        (surface (wl-window-wl-surface top)))
    (when (and damage surface (wl-window-configured top) (wl-window-mapped top)
               (null (wl-window-frame-callback top)))
      (let ((w (px-surface-width (wl-window-pixels top)))
            (h (px-surface-height (wl-window-pixels top))))
        ;; Buffers of another size are of no more use.
        (setf (wl-window-buffers top)
              (remove-if (lambda (b)
                           (unless (and (= (wl-shm-buffer-width b) w)
                                        (= (wl-shm-buffer-height b) h))
                             (wl-free-buffer b)
                             t))
                         (wl-window-buffers top)))
        (let ((buffer (or (find nil (wl-window-buffers top) :key #'wl-shm-buffer-busy)
                          (when (< (length (wl-window-buffers top)) 3)
                            (car (push (wl-make-buffer w h) (wl-window-buffers top)))))))
          ;; With every buffer still held by the compositor, the damage
          ;; waits for one to be released.
          (when buffer
            (dolist (b (wl-window-buffers top))
              (setf (wl-shm-buffer-stale b) (rect-union (wl-shm-buffer-stale b) damage)))
            (destructuring-bind (x0 y0 x1 y1) (wl-shm-buffer-stale buffer)
              (wl-composite top 0 0 buffer x0 y0 x1 y1))
            (setf (wl-shm-buffer-stale buffer) nil
                  (wl-shm-buffer-busy buffer) t
                  (wl-window-damage top) nil)
            (destructuring-bind (x0 y0 x1 y1) damage
              (wl-surface.attach surface (wl-shm-buffer-proxy buffer) 0 0)
              (wl-surface.damage-buffer surface x0 y0 (- x1 x0) (- y1 y0))
              ;; The buffer is in device pixels; the surface is the
              ;; window's logical size.
              (let ((viewport (wl-window-viewport top))
                    (size (cons (wl-window-width top) (wl-window-height top))))
                (when (and viewport (not (equal size (wl-window-viewport-size top))))
                  (wayflan-client.viewporter:wp-viewport.set-destination viewport (car size) (cdr size))
                  (setf (wl-window-viewport-size top) size)))
              (wl-request-frame top surface)
              (wl-surface.commit surface))
            t))))))

(defun wl-present-all ()
  (let ((dirty *wl-dirty-windows*))
    (setf *wl-dirty-windows* '())
    (dolist (top dirty)
      (unless (wl-present top)
        ;; Not shown yet: keep it for next time.
        (when (and (wl-window-damage top) (wl-window-mapped top))
          (pushnew top *wl-dirty-windows*))))))


;;; Showing and hiding top-level windows

(defvar *wl-focus-window* nil "The top-level window with the keyboard.")
(defvar *wl-pointer-window* nil "The top-level window the pointer is in.")
(defvar *wl-last-toplevel* nil "The top-level window last mapped or entered.")

(defun wl-popup-parent ()
  (let ((candidates (list *wl-pointer-window* *wl-focus-window* *wl-last-toplevel*)))
    (find-if (lambda (w)
               (and w (wl-window-mapped w) (wl-window-xdg-surface w)
                    (wl-window-configured w)))
             candidates)))

(defun wl-set-size-hints (win)
  (let ((tl (wl-window-xdg-toplevel win)))
    (when tl
      (xdg-toplevel.set-min-size tl (or (wl-window-min-width win) 0)
                                 (or (wl-window-min-height win) 0))
      (xdg-toplevel.set-max-size tl (or (wl-window-max-width win) 0)
                                 (or (wl-window-max-height win) 0)))))

(defun wl-handle-configure (win width height)
  "The compositor asks for WIN to be WIDTH by HEIGHT (0 leaves it to us)."
  (when (and (plusp width) (plusp height)
             (or (/= width (wl-window-width win)) (/= height (wl-window-height win))))
    (wl-resize-window win width height)
    (wl-queue-event (list :configure-notify win (wl-window-x win) (wl-window-y win)
                          width height))
    (wl-queue-event (list :expose win 0 0 width height))))

(defun wl-show-top-level (win)
  (if (wl-window-xdg-toplevel win)
      ;; Shown before: its surface was unmapped by committing no buffer.
      ;; Committing again asks for a configure, as the first time.
      (progn
        (setf (wl-window-configured win) nil
              (gethash (wl-window-wl-surface win) *wl-surface-to-window*) win)
        (wl-set-size-hints win)
        (wl-surface.commit (wl-window-wl-surface win))
        (setf *wl-last-toplevel* win))
      (wl-create-top-level win)))

(defun wl-create-top-level (win)
  (let* ((surface (wl-compositor.create-surface *wl-compositor*))
         (xdg-surface (xdg-wm-base.get-xdg-surface *wl-wm-base* surface))
         (pending-size nil))
    (setf (wl-window-wl-surface win) surface
          (wl-window-xdg-surface win) xdg-surface
          (wl-window-configured win) nil
          (gethash surface *wl-surface-to-window*) win)
    ;; Draw at the scale the compositor prefers for the surface, shown at
    ;; its logical size: both need both protocols.
    (when (and *wl-viewporter* *wl-fractional-scale-manager*)
      (let ((fractional (garnet-wl-protocols:wp-fractional-scale-manager-v1.get-fractional-scale
                         *wl-fractional-scale-manager* surface)))
        (setf (wl-window-viewport win) (wayflan-client.viewporter:wp-viewporter.get-viewport
                                                *wl-viewporter* surface)
              (wl-window-viewport-size win) nil
              (wl-window-fractional-scale win) fractional)
        (push (evlambda
                (:preferred-scale (scale)
                 (wl-set-scale (/ scale 120))))
              (wl-proxy-hooks fractional))))
    (let ((parent (and (eq (wl-window-kind win) :popup) (wl-popup-parent))))
      (if parent
          (let ((positioner (xdg-wm-base.create-positioner *wl-wm-base*)))
            (multiple-value-bind (vx vy) (wl-screen-origin parent)
              (xdg-positioner.set-size positioner (max 1 (wl-window-width win))
                                       (max 1 (wl-window-height win)))
              (xdg-positioner.set-anchor-rect positioner
                                              (- (wl-window-x win) vx)
                                              (- (wl-window-y win) vy) 1 1)
              (xdg-positioner.set-anchor positioner :top-left)
              (xdg-positioner.set-gravity positioner :bottom-right)
              ;; Let the compositor slide a menu back onto the screen.
              ;; slide_x | slide_y; the request takes a plain uint.
              (xdg-positioner.set-constraint-adjustment positioner 3))
            (let ((popup (xdg-surface.get-popup xdg-surface (wl-window-xdg-surface parent)
                                                positioner)))
              (destroy-proxy positioner)
              (setf (wl-window-xdg-popup win) popup)
              (push (evlambda
                      (:popup-done ()
                       ;; The compositor dismissed it; Opal still thinks it
                       ;; is shown, and will hide it in its own time.
                       nil))
                    (wl-proxy-hooks popup))))
          (let ((toplevel (xdg-surface.get-toplevel xdg-surface)))
            (setf (wl-window-xdg-toplevel win) toplevel)
            (xdg-toplevel.set-app-id toplevel "garnet")
            (when (wl-window-title win)
              (xdg-toplevel.set-title toplevel (wl-window-title win)))
            (wl-set-size-hints win)
            (push (evlambda
                    (:configure (width height states)
                     (declare (ignore states))
                     (setf pending-size (cons width height)))
                    (:close ()
                     (wl-queue-event (list :client-message win :wm-delete-window
                                           (make-array 5 :element-type '(unsigned-byte 32)
                                                         :initial-element 0)
                                           32))))
                  (wl-proxy-hooks toplevel)))))
    (push (evlambda
            (:configure (serial)
             (xdg-surface.ack-configure xdg-surface serial)
             (setf (wl-window-configured win) t)
             (when pending-size
               (wl-handle-configure win (car pending-size) (cdr pending-size))
               (setf pending-size nil))
             (wl-damage-all win)
             (wl-present win)))
          (wl-proxy-hooks xdg-surface))
    ;; The first commit, with no buffer, asks for the first configure.
    (wl-surface.commit surface)
    (unless (eq (wl-window-kind win) :popup)
      (setf *wl-last-toplevel* win))))

(defun wl-hide-top-level (win &optional destroy)
  "Unmap WIN's surface.  A top-level window keeps its Wayland objects to be
shown again, unless DESTROY; a popup's are destroyed, as it may be shown
next time at another place over another window."
  (let ((surface (wl-window-wl-surface win)))
    (when (and surface (wl-window-xdg-toplevel win) (not destroy))
      (wl-surface.attach surface nil 0 0)
      (wl-surface.commit surface)
      ;; A hidden surface's frame callback may never come.
      (setf (wl-window-configured win) nil
            (wl-window-frame-callback win) nil)
      (setf (wl-window-buffers win)
            (progn (mapc #'wl-free-buffer (wl-window-buffers win)) '()))
      (setf surface nil))
    (when surface
      (remhash surface *wl-surface-to-window*)
      (dolist (slot '(wl-window-viewport wl-window-fractional-scale
                      wl-window-xdg-popup wl-window-xdg-toplevel
                      wl-window-xdg-surface wl-window-wl-surface))
        (let ((proxy (funcall slot win)))
          (when proxy (ignore-errors (destroy-proxy proxy)))))
      (setf (wl-window-viewport win) nil
            (wl-window-fractional-scale win) nil
            (wl-window-viewport-size win) nil
            (wl-window-xdg-popup win) nil
            (wl-window-xdg-toplevel win) nil
            (wl-window-xdg-surface win) nil
            (wl-window-wl-surface win) nil
            (wl-window-configured win) nil
            (wl-window-frame-callback win) nil)
      ;; The buffers may still be on screen until the surface goes; free
      ;; them all, and start afresh when shown again.
      (mapc #'wl-free-buffer (wl-window-buffers win))
      (setf (wl-window-buffers win) '()))
    (when (eq *wl-last-toplevel* win) (setf *wl-last-toplevel* nil))))

(defun wl-map (win)
  (unless (wl-window-mapped win)
    (setf (wl-window-mapped win) t)
    (if (eq (wl-window-kind win) :child)
        (wl-damage-all win)
        (wl-show-top-level win))
    (wl-queue-event (list :map-notify win))
    (wl-queue-event (list :expose win 0 0 (wl-window-width win) (wl-window-height win)))))

(defun wl-unmap (win)
  (when (wl-window-mapped win)
    (setf (wl-window-mapped win) nil)
    (if (eq (wl-window-kind win) :child)
        (wl-damage (wl-window-parent win) (wl-window-x win) (wl-window-y win)
                   (wl-window-width win) (wl-window-height win))
        (wl-hide-top-level win))
    (wl-queue-event (list :unmap-notify win))))

(defun wl-resize-window (win width height)
  (let ((w (max 1 width)) (h (max 1 height)))
    (when (eq (wl-window-kind win) :child)
      ;; The area it leaves shows its parent again.
      (wl-damage (wl-window-parent win) (wl-window-x win) (wl-window-y win)
                 (wl-window-width win) (wl-window-height win)))
    (let ((pixels (wl-window-pixels win)))
      (px-resize-surface pixels (dev-size w (px-surface-scale pixels))
                         (dev-size h (px-surface-scale pixels)) (wl-window-background win))
      (setf (px-surface-logical-width pixels) w
            (px-surface-logical-height pixels) h))
    (setf (wl-window-width win) w
          (wl-window-height win) h)
    (wl-damage-all win)))


;;; Graphics contexts

(defun wl-resolve-function (function)
  "The raster function, 0 to 15, for FUNCTION: a number or an Opal draw
function keyword."
  (cond ((numberp function) function)
        ((and function (symbolp function) (get function :wl-draw-function)))
        ((cdr (assoc function *function-alist*)))
        (t +px-gx-copy+)))

(defun wl-color-to-pixel (color &optional (default 0))
  "An Opal color schema or a pixel as a #xRRGGBB pixel."
  (cond ((and color (schema-p color))
         (or (g-value color :colormap-index)
             (let ((r (round (* (or (g-value color :red) 0.0) 255)))
                   (g (round (* (or (g-value color :green) 0.0) 255)))
                   (b (round (* (or (g-value color :blue) 0.0) 255))))
               (logior (ash r 16) (ash g 8) b))))
        ((integerp color) color)
        (t default)))

(defun wl-line-style-val (style)
  (case style
    ((:dash :on-off-dash) :dash)
    (:double-dash :double-dash)
    (t :solid)))

(defun wl-get-stipple (style-schema root-window)
  "The depth-1 PX-SURFACE for the stipple of the Opal style STYLE-SCHEMA,
made once and kept on its stipple schema, enlarged for drawing at
*WL-SCALE* when that is 1.5 or more."
  (let ((stipple (wl-get-stipple-1 style-schema root-window))
        (factor (round *wl-scale*)))
    (if (or (null stipple) (<= factor 1))
        stipple
        (let* ((stipple-schema (g-value style-schema :stipple))
               (key (list :wl factor)))
          (or (getf (g-value stipple-schema :root-pixmap-plist) key)
              (let ((big (px-enlarge-surface stipple factor)))
                (s-value stipple-schema :root-pixmap-plist
                         (list* key big (g-value stipple-schema :root-pixmap-plist)))
                big))))))

(defun px-enlarge-surface (s factor)
  "A copy of S, each pixel FACTOR by FACTOR pixels."
  (let* ((w (px-surface-width s)) (h (px-surface-height s))
         (big (make-px-surface (* w factor) (* h factor) :depth (px-surface-depth s))))
    (dotimes (y (* h factor) big)
      (dotimes (x (* w factor))
        (setf (aref (px-surface-pixels big) (+ (* y w factor) x))
              (aref (px-surface-pixels s) (+ (* (floor y factor) w) (floor x factor))))))))

(defun wl-get-stipple-1 (style-schema root-window)
  (declare (ignore root-window))
  (let ((stipple-schema (and style-schema (schema-p style-schema)
                             (g-value style-schema :stipple))))
    (when stipple-schema
      (or (getf (g-value stipple-schema :root-pixmap-plist) :wl)
          (let ((image (or (g-value stipple-schema :image)
                           (let ((percent (g-value stipple-schema :percent)))
                             (when (numberp percent)
                               (wl-device-image nil (round (* (max 0 (min 100 percent)) 16)
                                                           100)))))))
            (when (wl-image-p image)
              (let ((pixmap (wl-create-pixmap nil (wl-image-width image)
                                              (wl-image-height image) 1 image t)))
                (s-value stipple-schema :root-pixmap-plist
                         (list* :wl pixmap (g-value stipple-schema :root-pixmap-plist)))
                pixmap)))))))

(defun set-wl-line-style (gc line-style root-window function)
  (let ((fn (wl-resolve-function function)))
    (setf (px-gc-function gc) fn)
    (when (and line-style (/= fn +px-gx-noop+))
      (setf (px-gc-foreground gc) (wl-color-to-pixel (g-value line-style :foreground-color) 0)
            (px-gc-background gc) (wl-color-to-pixel (g-value line-style :background-color)
                                                     #xFFFFFF))
      (unless (eq line-style (px-gc-opal-style gc))
        (setf (px-gc-opal-style gc) line-style
              (px-gc-logical-line-width gc) (or (g-value line-style :line-thickness) 0)
              (px-gc-line-style gc) (wl-line-style-val (g-value line-style :line-style))
              (px-gc-cap-style gc) (or (g-value line-style :cap-style) :butt)
              (px-gc-join-style gc) (or (g-value line-style :join-style) :miter)
              (px-gc-logical-dashes gc) (let ((d (g-value line-style :dash-pattern)))
                                          (if (and (consp d) (every #'plusp d)) d '(4 4)))
              (px-gc-dashes gc) (px-gc-logical-dashes gc)))
      ;; As in the CLX backend, a line style with a stipple is drawn
      ;; opaque-stippled.
      (let ((stipple (wl-get-stipple line-style root-window)))
        (setf (px-gc-stipple gc) stipple
              (px-gc-fill-style gc) (if stipple :opaque-stippled :solid))))))

(defun set-wl-filling-style (gc filling-style root-window function)
  (let ((fn (wl-resolve-function function)))
    (setf (px-gc-function gc) fn)
    (when (and filling-style (/= fn +px-gx-noop+))
      (setf (px-gc-foreground gc) (wl-color-to-pixel (g-value filling-style :foreground-color) 0)
            (px-gc-background gc) (wl-color-to-pixel (g-value filling-style :background-color)
                                                     #xFFFFFF))
      (unless (eq filling-style (px-gc-opal-style gc))
        (setf (px-gc-opal-style gc) filling-style
              (px-gc-fill-rule gc) (if (eq (g-value filling-style :fill-rule) :winding)
                                       :winding :even-odd)))
      (let ((stipple (wl-get-stipple filling-style root-window))
            (style (g-value filling-style :fill-style)))
        (setf (px-gc-stipple gc) stipple
              (px-gc-fill-style gc) (if (and stipple (member style '(:stippled :opaque-stippled
                                                                     :tiled)))
                                        style
                                        :solid))))))

(defun wl-line-gc (window)
  (or (let ((di (g-value window :display-info))) (and di (display-info-line-style-gc di)))
      *wl-line-gc*))

(defun wl-fill-gc (window)
  (or (let ((di (g-value window :display-info))) (and di (display-info-filling-style-gc di)))
      *wl-fill-gc*))


;;; Device Initialization & Connection

(defvar *wl-xkb-context* nil)
(defvar *wl-xkb-keymap* nil)
(defvar *wl-xkb-state* nil)

(defun wl-null-pointer-p (p)
  (or (null p) (cffi:null-pointer-p p)))

(defun wl-bind-globals ()
  (let ((registry (wl-display.get-registry *wl-display*)))
    (push (evlambda
            (:global (name interface version)
             (let ((class (let ((it (find-interface-named interface)))
                            (and it (class-name it)))))
               (case class
                 (wl-compositor
                  (setf *wl-compositor* (wl-registry.bind registry name 'wl-compositor
                                                          (min version 4))))
                 (wl-shm
                  (setf *wl-shm* (wl-registry.bind registry name 'wl-shm 1)))
                 (xdg-wm-base
                  (let ((base (wl-registry.bind registry name 'xdg-wm-base 1)))
                    (setf *wl-wm-base* base)
                    (push (evlambda
                            (:ping (serial) (xdg-wm-base.pong base serial)))
                          (wl-proxy-hooks base))))
                 (wl-seat
                  (unless *wl-seat*
                    (setf *wl-seat* (wl-registry.bind registry name 'wl-seat
                                                      (min version 5)))
                    (push 'wl-handle-seat (wl-proxy-hooks *wl-seat*))))
                 (wl-data-device-manager
                  (setf *wl-data-device-manager*
                        (wl-registry.bind registry name 'wl-data-device-manager
                                          (min version 3))))
                 (wayflan-client.viewporter:wp-viewporter
                  (setf *wl-viewporter*
                        (wl-registry.bind registry name 'wayflan-client.viewporter:wp-viewporter 1)))
                 (garnet-wl-protocols:wp-fractional-scale-manager-v1
                  (setf *wl-fractional-scale-manager*
                        (wl-registry.bind registry name
                                          'garnet-wl-protocols:wp-fractional-scale-manager-v1 1)))
                 (garnet-wl-protocols:wp-cursor-shape-manager-v1
                  (setf *wl-cursor-shape-manager*
                        (wl-registry.bind registry name
                                          'garnet-wl-protocols:wp-cursor-shape-manager-v1
                                          1)))))))
          (wl-proxy-hooks registry))
    ;; One roundtrip for the globals, another for the seat's capabilities.
    (wl-display-roundtrip *wl-display*)
    (wl-display-roundtrip *wl-display*)
    (unless (and *wl-compositor* *wl-shm* *wl-wm-base*)
      (error "The Wayland compositor lacks wl_compositor, wl_shm or xdg_wm_base."))
    (when (and *wl-data-device-manager* *wl-seat*)
      (setf *wl-data-device*
            (wl-data-device-manager.get-data-device *wl-data-device-manager* *wl-seat*))
      (push 'wl-handle-data-device (wl-proxy-hooks *wl-data-device*)))))

(defun wl-handle-seat (&rest event)
  (event-case event
    (:capabilities (capabilities)
     (if (member :pointer capabilities)
         (unless *wl-pointer*
           (setf *wl-pointer* (wl-seat.get-pointer *wl-seat*))
           (push 'wl-handle-pointer (wl-proxy-hooks *wl-pointer*))
           (when *wl-cursor-shape-manager*
             (setf *wl-cursor-shape-device*
                   (garnet-wl-protocols:wp-cursor-shape-manager-v1.get-pointer
                    *wl-cursor-shape-manager* *wl-pointer*))))
         (when *wl-pointer*
           (when *wl-cursor-shape-device*
             (ignore-errors (destroy-proxy *wl-cursor-shape-device*))
             (setf *wl-cursor-shape-device* nil))
           (ignore-errors (destroy-proxy *wl-pointer*))
           (setf *wl-pointer* nil)))
     (if (member :keyboard capabilities)
         (unless *wl-keyboard*
           (setf *wl-keyboard* (wl-seat.get-keyboard *wl-seat*))
           (push 'wl-handle-keyboard (wl-proxy-hooks *wl-keyboard*)))
         (when *wl-keyboard*
           (ignore-errors (destroy-proxy *wl-keyboard*))
           (setf *wl-keyboard* nil))))))

(defun wl-make-gc ()
  (make-px-gc :function +px-gx-copy+ :foreground 0 :background #xFFFFFF))

(defun wl-connect ()
  (setf *wl-display* (wl-display-connect)
        *wl-thread* (bt:current-thread))
  (multiple-value-bind (r w) (wl-make-wake-pipe)
    (setf *wl-wake-read-fd* r *wl-wake-write-fd* w))
  (setf *wl-xkb-context* (xkb:xkb-context-new ()))
  (wl-bind-globals)
  (setf *wl-root* (make-wl-window :kind :root :mapped t
                                  :width *screen-width* :height *screen-height*
                                  :pixels (make-px-surface 1 1))
        *wl-line-gc* (wl-make-gc)
        *wl-fill-gc* (wl-make-gc))
  (setf (display-info-display *display-info*) *wl-display*
        (display-info-screen *display-info*) nil
        (display-info-root-window *display-info*) *wl-root*
        (display-info-line-style-gc *display-info*) *wl-line-gc*
        (display-info-filling-style-gc *display-info*) *wl-fill-gc*)
  (setf *white* #xFFFFFF *black* 0 *color-screen-p* :true-color)
  t)

(defun wl-set-draw-function-alist (root-window)
  (declare (ignore root-window))
  (setq *function-alist*
        '((:clear . 0) (:and . 1) (:and-reverse . 2) (:copy . 3)
          (:and-inverted . 4) (:no-op . 5) (:xor . 6) (:or . 7)
          (:nor . 8) (:equiv . 9) (:invert . 10) (:or-reverse . 11)
          (:copy-inverted . 12) (:or-inverted . 13) (:nand . 14) (:set . 15)))
  (setq *copy* +px-gx-copy+))

(defun wl-set-draw-functions (root-window)
  (gem:set-draw-function-alist root-window)
  (dolist (fn-pair *function-alist*)
    (setf (get (car fn-pair) :wl-draw-function) (cdr fn-pair))))

(defun init-wl-device ()
  (attach-wl-methods wl-device)
  (s-value device-info :current-root *root-window*)
  (s-value device-info :current-device wl-device)
  (pushnew wl-device (g-value device-info :active-devices))
  (set-draw-functions *root-window*)
  *root-window*)

(defun init-wl-device-post ()
  (wl-connect)
  (s-value *root-window* :drawable *wl-root*)
  (s-value *root-window* :display-info *display-info*)
  ;; Opal's fonts were made when Garnet's core was loaded, before there was
  ;; a device, and their metrics computed by GEM's fallbacks.  Their
  ;; formulas depend on :CURRENT-ROOT, which init set to the value it
  ;; already had, so nothing was invalidated: change it, to have them
  ;; computed again by this backend.
  (s-value device-info :current-root nil)
  (s-value device-info :current-root *root-window*))


;;; Window Lifecycle & Window Properties

(defvar *wl-window-buffers* (trivial-garbage:make-weak-hash-table :weakness :key :test 'eq)
  "The double buffers of windows, drawn at *WL-SCALE* like the windows.")

(defun wl-set-drawable-to-window (window drawable)
  ;; Opal says so of a window's drawable, and of its double buffer, which
  ;; is then drawn at the window's scale too.
  (when (px-surface-p drawable)
    (setf (gethash drawable *wl-window-buffers*) t)
    (unless (= (px-surface-scale drawable) *wl-scale*)
      (wl-rescale-surface drawable *wl-scale* #xFFFFFF)))
  (setf (gethash drawable *wl-drawable-to-window-table*) window))

(defun wl-drawable-to-window (root-window drawable)
  (declare (ignore root-window))
  (gethash drawable *wl-drawable-to-window-table*))

(defun wl-window-from-drawable (root-window drawable)
  (declare (ignore root-window))
  (gethash drawable *wl-drawable-to-window-table*))

(defun wl-drawable-equal (root-window d1 d2)
  (declare (ignore root-window))
  (eq d1 d2))

(defun wl-check-wm-delete-window (root-window type data format)
  (declare (ignore root-window data format))
  (eq type :wm-delete-window))

(defun wl-make-window-surface (width height background)
  "A surface for a window, or its double buffer, WIDTH by HEIGHT logical
pixels, drawn at *WL-SCALE*."
  (let ((s (make-px-surface (dev-size width *wl-scale*) (dev-size height *wl-scale*)
                            :initial background)))
    (setf (px-surface-scale s) *wl-scale*
          (px-surface-logical-width s) (max 1 width)
          (px-surface-logical-height s) (max 1 height))
    s))

(defun wl-rescale-surface (s k background)
  "Give S, a window's surface or double buffer, scale K, cleared to
BACKGROUND: what was drawn at the old scale would show through where Opal
does not draw again."
  (setf (px-surface-scale s) k)
  (px-resize-surface s (dev-size (px-surface-logical-width s) k)
                     (dev-size (px-surface-logical-height s) k) background)
  (fill (px-surface-pixels s) background))

(defun wl-create-window (parent-window x y width height title icon-name
                         background border-width save-under visible
                         min-width min-height max-width max-height
                         user-specified-position-p user-specified-size-p
                         override-redirect)
  ;; As with X, the window is not mapped here: Opal maps it afterwards.
  (declare (ignore icon-name border-width save-under visible
                   user-specified-position-p user-specified-size-p))
  (let* ((parent (or (and parent-window (g-value parent-window :drawable)) *wl-root*))
         (top-level (eq (wl-window-kind parent) :root))
         (bg (if (integerp background) background #xFFFFFF))
         (win (make-wl-window
               :kind (cond ((not top-level) :child)
                           ((eq override-redirect :on) :popup)
                           (t :toplevel))
               :parent parent
               :x (or x 0) :y (or y 0)
               :width (max 1 (or width 1)) :height (max 1 (or height 1))
               :background bg
               :pixels (wl-make-window-surface (or width 1) (or height 1) bg)
               :title (and title (string title))
               :override-redirect (eq override-redirect :on)
               :min-width min-width :min-height min-height
               :max-width max-width :max-height max-height)))
    (unless top-level
      (setf (wl-window-children parent) (append (wl-window-children parent) (list win))))
    win))

(defun wl-delete-window (root-window drawable)
  (declare (ignore root-window))
  (when (wl-window-p drawable)
    (labels ((forget (w)
               (mapc #'forget (wl-window-children w))
               (remhash w *wl-drawable-to-window-table*)
               (setf *wl-dirty-windows* (delete w *wl-dirty-windows*))))
      (wl-unmap drawable)
      (wl-hide-top-level drawable t)
      (let ((parent (wl-window-parent drawable)))
        (when (and parent (eq (wl-window-kind drawable) :child))
          (setf (wl-window-children parent) (remove drawable (wl-window-children parent)))))
      (forget drawable))))

(defun wl-map-and-wait (window drawable)
  (declare (ignore window))
  (when (wl-window-p drawable)
    (wl-map drawable)))

(defun wl-reparent (window new-parent drawable left top)
  (declare (ignore window))
  (when (wl-window-p drawable)
    (let ((was-mapped (wl-window-mapped drawable))
          (old-parent (wl-window-parent drawable))
          (parent (or (and new-parent (g-value new-parent :drawable)) *wl-root*)))
      (wl-unmap drawable)
      (when (and old-parent (eq (wl-window-kind drawable) :child))
        (setf (wl-window-children old-parent) (remove drawable (wl-window-children old-parent))))
      (setf (wl-window-parent drawable) parent
            (wl-window-x drawable) left
            (wl-window-y drawable) top)
      (if (eq (wl-window-kind parent) :root)
          (setf (wl-window-kind drawable)
                (if (wl-window-override-redirect drawable) :popup :toplevel))
          (setf (wl-window-kind drawable) :child
                (wl-window-children parent) (append (wl-window-children parent)
                                                    (list drawable))))
      (when was-mapped (wl-map drawable)))))

(defun wl-raise-or-lower (window raisep)
  (let ((drawable (g-value window :drawable)))
    (when (and (wl-window-p drawable) (eq (wl-window-kind drawable) :child))
      (let* ((parent (wl-window-parent drawable))
             (others (remove drawable (wl-window-children parent))))
        (setf (wl-window-children parent)
              (if raisep (append others (list drawable)) (cons drawable others)))
        (wl-damage-all drawable)))))

(defun wl-initialize-window-borders (window drawable)
  (declare (ignore drawable))
  ;; The compositor draws any decorations outside the window.
  (s-value window :left-border-width 0)
  (s-value window :top-border-width 0)
  (s-value window :right-border-width 0)
  (s-value window :bottom-border-width 0)
  (s-value window :total-border-width 0))

(defun wl-move-window (win x y)
  (unless (and (= x (wl-window-x win)) (= y (wl-window-y win)))
    (if (eq (wl-window-kind win) :child)
        (progn
          (wl-damage (wl-window-parent win) (wl-window-x win) (wl-window-y win)
                     (wl-window-width win) (wl-window-height win))
          (setf (wl-window-x win) x (wl-window-y win) y)
          (wl-damage-all win))
        ;; A client cannot move its windows on Wayland: keep the position
        ;; as Opal's idea of it.
        (setf (wl-window-x win) x (wl-window-y win) y))))

(defun wl-set-window-property (window property value)
  (let ((drawable (g-value window :drawable)))
    (when (wl-window-p drawable)
      (case property
        (:left (wl-move-window drawable value (wl-window-y drawable)))
        (:top (wl-move-window drawable (wl-window-x drawable) value))
        (:width
         (unless (= (max 1 value) (wl-window-width drawable))
           (wl-resize-window drawable value (wl-window-height drawable))))
        (:height
         (unless (= (max 1 value) (wl-window-height drawable))
           (wl-resize-window drawable (wl-window-width drawable) value)))
        (:visible
         (case value
           ((nil) (wl-unmap drawable))
           (:iconified
            (if (wl-window-xdg-toplevel drawable)
                (xdg-toplevel.set-minimized (wl-window-xdg-toplevel drawable))
                (wl-map drawable)))
           (t (wl-map drawable))))
        (:title
         (setf (wl-window-title drawable) (and value (string value)))
         (when (and value (wl-window-xdg-toplevel drawable))
           (xdg-toplevel.set-title (wl-window-xdg-toplevel drawable) (string value))))
        (:event-mask
         (setf (wl-window-event-mask drawable) value))
        (:cursor
         (setf (wl-window-cursor drawable) value)
         (wl-update-cursor))
        (:buffer-gcontext
         (destructuring-bind (buffer foreground background) value
           (declare (ignore buffer))
           (s-value window :buffer-gcontext
                    (make-px-gc :function +px-gx-copy+
                                :foreground (or foreground 0)
                                :background (or background #xFFFFFF)))))
        (:background-color
         ;; Opal also sends :ON/:OFF here for :SAVE-UNDER; those are not colors.
         (when (or (null value) (schema-p value))
           (let ((pixel (wl-color-to-index window value))
                 (buffer-gc (g-value window :buffer-gcontext)))
             (setf (wl-window-background drawable) pixel)
             (when buffer-gc
               (setf (px-gc-background buffer-gc) pixel))))))))
  nil)

(defun wl-translate-coordinates (root-window window1 x y &optional window2)
  (declare (ignore root-window))
  (flet ((origin (w)
           (let ((d (cond ((null w) nil)
                          ((wl-window-p w) w)
                          ((schema-p w) (g-value w :drawable)))))
             (if (wl-window-p d) (wl-screen-origin d) (values 0 0)))))
    (multiple-value-bind (x1 y1) (origin window1)
      (multiple-value-bind (x2 y2) (origin window2)
        (values (- (+ x x1) x2) (- (+ y y1) y2))))))

(defvar *wl-grab* nil
  "The WL-WINDOW an active pointer grab sends events to, or NIL.")

(defun wl-mouse-grab (window grabp want-enter-leave &optional (ownerp t))
  "Grab the pointer for WINDOW, or let go.  As with X's owner-events grab
(OWNERP true, as Opal grabs), the pointer's events still go to the window
of ours under it; and on Wayland, a client gets no events from outside its
windows anyway.  So only a grab without OWNERP sends them all to WINDOW.
OWNERP :CHANGE changes the event mask of the grab there is, which here is
the window's own."
  (declare (ignore want-enter-leave))
  (cond ((eq ownerp :change) nil)
        ((not grabp) (setf *wl-grab* nil))
        ((not ownerp)
         (let ((d (g-value window :drawable)))
           (when (wl-window-p d)
             (setf *wl-grab* d))))))

(defun wl-window-debug-id (window)
  (g-value window :drawable))

(defun wl-window-depth (window)
  (declare (ignore window))
  24)

(defun wl-window-has-grown (window width height)
  "Whether the window's buffer is smaller than WIDTH by HEIGHT."
  (let ((buffer (g-value window :buffer)))
    (and (px-surface-p buffer)
         (or (> width (px-surface-logical-width buffer))
             (> height (px-surface-logical-height buffer))))))

(defun wl-device-batch-changes (root-window drawable function)
  (declare (ignore root-window drawable))
  (funcall function))

(defun wl-flush-output (window)
  (declare (ignore window))
  (when *wl-display*
    (if (eq (bt:current-thread) *wl-thread*)
        (wl-present-all)
        ;; A timer thread, after queuing an event: wake the event loop,
        ;; which shows what has changed.
        (wl-poke-pipe *wl-wake-write-fd*))))

(defun wl-beep (root-window)
  ;; Wayland has no core bell.
  (declare (ignore root-window))
  nil)

(defun wl-all-garnet-windows ()
  (let ((result nil))
    (maphash (lambda (k v) (declare (ignore k)) (pushnew v result))
             *wl-drawable-to-window-table*)
    result))

(defun wl-black-white-pixel (window)
  (declare (ignore window))
  (values 0 #xFFFFFF))

(defun wl-color-to-index (root-window a-color)
  (declare (ignore root-window))
  (if a-color
      (wl-color-to-pixel a-color #xFFFFFF)
      #xFFFFFF))

(defun wl-colormap-property (root-window property &optional a b c)
  "Colors are 24-bit #xRRGGBB pixels, as in the XCB backend."
  (declare (ignore root-window))
  (flet ((channel (x) (round (* 255 (max 0 (min 1 (float x 1.0)))))))
    (case property
      (:color-lookup (values 0 0 0))
      (:make-color (logior (ash (channel a) 16) (ash (channel b) 8) (channel c)))
      (:alloc-color a)
      (:query-colors (values (* 257 (ldb (byte 8 16) a))
                             (* 257 (ldb (byte 8 8) a))
                             (* 257 (ldb (byte 8 0) a))))
      (t (error "Unknown property ~S in gem::wl-colormap-property" property)))))

(defun wl-query-color (root-window pixel)
  (declare (ignore root-window))
  (values (ldb (byte 8 16) pixel) (ldb (byte 8 8) pixel) (ldb (byte 8 0) pixel)))


;;; Shape Rendering & Drawing Primitives
;;;
;;; Opal's coordinates are logical; each primitive is mapped to the device
;;; pixels of the surface drawn on, at its scale K (see DEV-EDGE).

(defun wl-clear-area (window &optional (x 0) (y 0) width height clear-buffer-p)
  "Clear an area of WINDOW to its background.  If CLEAR-BUFFER-P, clear its
double buffer instead: the whole buffer when X is NIL."
  (if clear-buffer-p
      (let ((buffer (g-value window :buffer))
            (buffer-gc (g-value window :buffer-gcontext)))
        (when (and (px-surface-p buffer) buffer-gc)
          (if x
              (multiple-value-bind (dx dy dw dh) (dev-rect x y width height (px-surface-scale buffer))
                (px-clear-rectangle buffer dx dy dw dh (px-gc-background buffer-gc)))
              (px-clear-rectangle buffer 0 0 (px-surface-width buffer)
                                  (px-surface-height buffer) (px-gc-background buffer-gc)))))
      (let ((drawable (g-value window :drawable)))
        (when (wl-window-p drawable)
          (let ((x (or x 0)) (y (or y 0))
                (w (or width (wl-window-width drawable)))
                (h (or height (wl-window-height drawable))))
            (multiple-value-bind (dx dy dw dh) (dev-rect x y w h (wl-scale-of drawable))
              (px-clear-rectangle (wl-window-pixels drawable) dx dy dw dh
                                  (wl-window-background drawable)))
            (wl-damage drawable x y w h))))))

(defun wl-draw-rectangle (window left top width height function line-style fill-style)
  (let* ((width (max 1 width)) (height (max 1 height))
         (drawable (the-drawable window))
         (s (wl-target drawable))
         (k (px-surface-scale s))
         (thickness (if line-style (max (or (g-value line-style :line-thickness) 0) 1) 0)))
    (when fill-style
      (let ((gc (wl-gc-device (wl-fill-gc window) k)))
        (set-wl-filling-style gc fill-style nil function)
        (multiple-value-bind (dx dy dw dh)
            (dev-rect (+ left thickness) (+ top thickness)
                      (max 0 (- width (* 2 thickness))) (max 0 (- height (* 2 thickness))) k)
          (px-fill-rectangle s gc dx dy dw dh))))
    (when line-style
      (let ((gc (wl-line-gc window))
            (half (truncate thickness 2)))
        (set-wl-line-style gc line-style nil function)
        (wl-gc-device gc k)
        ;; The outline runs through the centres of its corner pixels.
        (let ((x0 (dev-vertex (+ left half) k))
              (y0 (dev-vertex (+ top half) k))
              (x1 (dev-vertex (+ left half (max 0 (- width thickness))) k))
              (y1 (dev-vertex (+ top half (max 0 (- height thickness))) k)))
          (px-rectangle-outline s gc x0 y0 (- x1 x0) (- y1 y0)))))
    (wl-note-drawn drawable (1- left) (1- top) (+ width 2) (+ height 2))))

(defun wl-points-bbox-damage (drawable points line-width)
  (when (and points (wl-window-p drawable))
    (let ((pad (+ 2 (ceiling (or line-width 0) 2)))
          (x0 (reduce #'min points :key #'car)) (x1 (reduce #'max points :key #'car))
          (y0 (reduce #'min points :key #'cdr)) (y1 (reduce #'max points :key #'cdr)))
      (wl-note-drawn drawable (- x0 pad) (- y0 pad)
                     (+ (- x1 x0) pad pad 1) (+ (- y1 y0) pad pad 1)))))

(defun wl-points-from-list (point-list)
  "Flat coordinates (X0 Y0 X1 Y1 ...) as a list of (X . Y)."
  (loop for (x y) on point-list by #'cddr
        when (and x y) collect (cons (round x) (round y))))

(defun dev-points (points k)
  "Logical points (X . Y) as device points, at their pixels' centres:
integers at scale 1, for X's thin lines, else exact."
  (if (= k 1)
      points
      (loop for (x . y) in points collect (cons (dev-centre x k) (dev-centre y k)))))

(defun dev-vertex (v k)
  (if (= k 1) v (dev-centre v k)))

(defun wl-draw-line (window x1 y1 x2 y2 function line-style &optional drawable)
  (let* ((drawable (or drawable (the-drawable window)))
         (k (wl-scale-of drawable)))
    (when line-style
      (let ((gc (wl-line-gc window)))
        (set-wl-line-style gc line-style nil function)
        (wl-gc-device gc k)
        (px-segment (wl-target drawable) gc
                    (dev-vertex x1 k) (dev-vertex y1 k)
                    (dev-vertex x2 k) (dev-vertex y2 k))
        (wl-points-bbox-damage drawable (list (cons x1 y1) (cons x2 y2))
                               (px-gc-logical-line-width gc))))))

(defun wl-draw-lines (window point-list function line-style fill-style)
  (let* ((drawable (the-drawable window))
         (s (wl-target drawable))
         (k (px-surface-scale s))
         (points (wl-points-from-list point-list)))
    (when points
      (when fill-style
        (let ((gc (wl-gc-device (wl-fill-gc window) k)))
          (set-wl-filling-style gc fill-style nil function)
          (px-fill-polygon s gc (loop for (x . y) in points
                                      collect (dev-centre x k) collect (dev-centre y k)))))
      (when line-style
        (let ((gc (wl-line-gc window)))
          (set-wl-line-style gc line-style nil function)
          (wl-gc-device gc k)
          (px-polyline s gc (dev-points points k))))
      (wl-points-bbox-damage drawable points
                             (and line-style (g-value line-style :line-thickness))))))

(defun wl-draw-points (window point-list function line-style)
  (let* ((drawable (the-drawable window))
         (s (wl-target drawable))
         (k (px-surface-scale s))
         (points (wl-points-from-list point-list)))
    (when (and line-style points)
      (let ((gc (wl-line-gc window)))
        (set-wl-line-style gc line-style nil function)
        (wl-gc-device gc k)
        (loop for (x . y) in points
              do (if (= k 1)
                     (px-point s gc x y)
                     (multiple-value-bind (dx dy dw dh) (dev-rect x y 1 1 k)
                       (px-fill-rectangle s gc dx dy dw dh))))
        (wl-points-bbox-damage drawable points 0)))))

(defun wl-draw-arc (window x y width height angle1 angle2 function
                    line-style fill-style &optional pie-slice-p)
  (declare (ignore pie-slice-p))
  (let* ((drawable (the-drawable window))
         (s (wl-target drawable))
         (k (px-surface-scale s))
         (thickness (if line-style (max 1 (or (g-value line-style :line-thickness) 0)) 0)))
    (flet ((arc-box (bx by bw bh)
             ;; X's arc box runs between pixel centres.
             (values (dev-centre bx k) (dev-centre by k) (* bw k) (* bh k))))
      (when fill-style
        (let ((gc (wl-gc-device (wl-fill-gc window) k)))
          (set-wl-filling-style gc fill-style nil function)
          (multiple-value-bind (ax ay aw ah)
              (arc-box (+ x thickness) (+ y thickness)
                       (max 0 (- width (* 2 thickness))) (max 0 (- height (* 2 thickness))))
            (px-arc-fill s gc ax ay aw ah angle1 angle2))))
      (when line-style
        (let ((gc (wl-line-gc window))
              (half (truncate thickness 2)))
          (set-wl-line-style gc line-style nil function)
          (wl-gc-device gc k)
          (multiple-value-bind (ax ay aw ah)
              (arc-box (+ x half) (+ y half)
                       (max 0 (- width thickness)) (max 0 (- height thickness)))
            (px-arc-outline s gc ax ay aw ah angle1 angle2)))))
    (wl-note-drawn drawable (- x thickness 1) (- y thickness 1)
                   (+ width thickness thickness 2) (+ height thickness thickness 2))))

(defun wl-draw-roundtangle (window left top width height x-radius y-radius function
                            line-style fill-style)
  "A rectangle with rounded corners, as the XCB backend draws it, from
rectangles, segments and quarter arcs."
  (let* ((drawable (the-drawable window))
         (s (wl-target drawable))
         (k (px-surface-scale s))
         (th (if line-style (max 1 (or (g-value line-style :line-thickness) 0)) 0))
         (th/2 (floor th 2))
         (th\2 (ceiling th 2))
         (c-w (+ x-radius x-radius))
         (c-h (+ y-radius y-radius))
         (quarter (/ pi 2)))
    (when fill-style
      (let ((gc (wl-gc-device (wl-fill-gc window) k)))
        (set-wl-filling-style gc fill-style nil function)
        ;; One path, filled by the winding rule, so overlapping pieces are
        ;; not painted twice.
        (let* ((x0 (+ left th)) (y0 (+ top th))
               (x1 (- (+ left width) th)) (y1 (- (+ top height) th))
               (rx (max 0 (- x-radius th))) (ry (max 0 (- y-radius th)))
               (coords '()))
          (flet ((corner (cx cy from)
                   (loop for i from 0 to 8
                         for a = (+ from (* quarter (/ i 8)))
                         do (push (dev-centre (+ cx (* rx (cos a))) k) coords)
                            (push (dev-centre (- cy (* ry (sin a))) k) coords))))
            (corner (- x1 rx) (+ y0 ry) 0)
            (corner (+ x0 rx) (+ y0 ry) quarter)
            (corner (+ x0 rx) (- y1 ry) pi)
            (corner (- x1 rx) (- y1 ry) (* 3 quarter)))
          (px-fill-polygon s gc (nreverse coords) :winding))))
    (when line-style
      (let ((gc (wl-line-gc window))
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
        (set-wl-line-style gc line-style nil function)
        (wl-gc-device gc k)
        (flet ((seg (xa ya xb yb)
                 (px-segment s gc (dev-vertex xa k) (dev-vertex ya k)
                             (dev-vertex xb k) (dev-vertex yb k)))
               (arc (ax ay a1)
                 (px-arc-outline s gc (dev-centre ax k) (dev-centre ay k)
                                 (* c-w-line k) (* c-h-line k) a1 quarter)))
          (seg left-w y right y)
          (seg left-w y1 right y1)
          (seg l up l down)
          (seg l1 up l1 down)
          (let ((arc-left (+ left th\2 (if (< th 2) -1 0)))
                (arc-right (+ left width (- c-w-line) (- th\2) (if (< th 2) 0 -1)))
                (arc-bottom (+ top height (- c-h-line) (- th\2) (if (<= th 3) 0 -1))))
            (arc arc-right (+ top th/2) 0)
            (arc arc-left (+ top th/2) quarter)
            (arc arc-left arc-bottom pi)
            (arc arc-right arc-bottom (* 3 quarter))))))
    (wl-note-drawn drawable (- left th 1) (- top th 1) (+ width th th 2) (+ height th th 2))))

(defun wl-set-clip-mask (window clip-mask &optional lstyle-ogc fstyle-ogc)
  (let ((clip (if (or (null clip-mask) (eq clip-mask :none))
                  :none
                  ;; Copy: Opal reuses its clip-mask lists and changes them
                  ;; in place.
                  (loop for (x y w h) on clip-mask by #'cddddr
                        collect (list x y (max 1 w) (max 1 h))))))
    (dolist (gc (list (or lstyle-ogc (wl-line-gc window)) (or fstyle-ogc (wl-fill-gc window))))
      (setf (px-gc-logical-clip gc) clip
            (px-gc-clip gc) clip
            (px-gc-clip-scale gc) 1))))

(defun wl-bit-blit (window source s-x s-y width height destination d-x d-y)
  (when (and source destination)
    (let* ((gc (or (g-value window :buffer-gcontext) (wl-line-gc window)))
           (src (wl-target source)) (dst (wl-target destination))
           (ks (px-surface-scale src)) (kd (px-surface-scale dst)))
      (wl-gc-device gc kd)
      (let ((fn (px-gc-function gc)))
        (when (eq gc (wl-line-gc window)) (setf (px-gc-function gc) +px-gx-copy+))
        (unwind-protect
             (if (= ks kd)
                 (multiple-value-bind (sx sy sw sh) (dev-rect s-x s-y width height ks)
                   (multiple-value-bind (dx dy) (dev-rect d-x d-y width height kd)
                     (px-copy-area src dst gc sx sy sw sh dx dy)))
                 ;; A pixmap of another scale: resample it.
                 (multiple-value-bind (dx dy dw dh) (dev-rect d-x d-y width height kd)
                   (px-copy-area (px-resample src (dev-edge s-x ks) (dev-edge s-y ks)
                                              (dev-size width ks) (dev-size height ks) dw dh)
                                 dst gc 0 0 dw dh dx dy)))
          (setf (px-gc-function gc) fn)))
      (wl-note-drawn destination d-x d-y width height))))

(defun px-resample (s x y w h dw dh)
  "The W by H area of S at (X, Y), resampled to DW by DH, nearest pixel."
  (let ((out (make-px-surface dw dh :depth (px-surface-depth s)))
        (sw (px-surface-width s)) (sh (px-surface-height s)))
    (dotimes (r dh out)
      (dotimes (c dw)
        (let ((sx (+ x (floor (* c w) dw))) (sy (+ y (floor (* r h) dh))))
          (when (and (< -1 sx sw) (< -1 sy sh))
            (setf (aref (px-surface-pixels out) (+ (* r dw) c))
                  (aref (px-surface-pixels s) (+ (* sy sw) sx)))))))))


;;; Fonts and Text, with Runes

(defparameter *wl-truetype-initialized-p* nil)
(defparameter *wl-font-cache-table* (make-hash-table :test 'equal))
(defparameter *wl-layout-cache* (make-hash-table :test 'equal)
  "(font . string) -> its glyph layout.  Opal draws the same strings again
and again, and laying one out takes the font loader's lock and exact
arithmetic on every glyph.")


(defun ensure-wl-truetype-initialized ()
  (unless *wl-truetype-initialized-p*
    (runes:cache-fonts)
    (setf *wl-truetype-initialized-p* t)))

(defun wl-resolve-font-family-and-subfamily (family face)
  "An installed TrueType family and subfamily for Garnet's FAMILY and FACE."
  (ensure-wl-truetype-initialized)
  (let* ((all-fams (runes:get-font-families))
         (fam (flet ((pick (&rest names)
                       (or (loop for n in names
                                 thereis (find n all-fams :test #'string-equal))
                           (first all-fams))))
                (cond ((stringp family) (pick family))
                      ((eq family :serif) (pick "DejaVu Serif" "Liberation Serif"))
                      ((eq family :sans-serif) (pick "DejaVu Sans" "Liberation Sans"))
                      (t (pick "DejaVu Sans Mono" "Liberation Mono")))))
         (subs (runes:get-font-subfamilies fam))
         (sub (flet ((pick (&rest names)
                       (or (loop for n in names thereis (find n subs :test #'string-equal))
                           (first subs))))
                (case face
                  (:bold (pick "Bold"))
                  (:italic (pick "Italic" "Oblique"))
                  (:bold-italic (pick "Bold Italic" "Bold Oblique"))
                  (t (pick "Regular" "Book"))))))
    (values fam sub)))

(defun wl-make-truetype-font (family face size)
  (multiple-value-bind (fam sub) (wl-resolve-font-family-and-subfamily family face)
    (make-instance 'runes:font
                   :family fam :subfamily sub
                   :size (cond ((numberp size) size)
                               ((eq size :small) 10)
                               ((eq size :large) 16)
                               ((eq size :very-large) 20)
                               (t 12))
                   :antialias t)))

(defun wl-font-to-internal (root-window opal-font)
  "The Runes font for a Garnet font schema or descriptor."
  (declare (ignore root-window))
  (ensure-wl-truetype-initialized)
  (flet ((cached (key family face size)
           (or (gethash key *wl-font-cache-table*)
               (setf (gethash key *wl-font-cache-table*)
                     (wl-make-truetype-font family face size)))))
    (cond
      ((typep opal-font 'runes:font) opal-font)
      ((and opal-font (schema-p opal-font))
       (let* ((fam (or (g-value opal-font :family) :fixed))
              (fac (or (g-value opal-font :face) :roman))
              (sz (or (g-value opal-font :size) :medium))
              (inst (cached (list fam fac sz) fam fac sz)))
         (s-value opal-font :xfont inst)
         inst))
      ((listp opal-font)
       (cached (list (first opal-font) (second opal-font) (third opal-font))
               (first opal-font) (second opal-font) (third opal-font)))
      (t (cached :default :fixed :roman :medium)))))

(defun wl-resolve-font (root-window font)
  (if (typep font 'runes:font)
      font
      (or (and (schema-p font) (let ((f (g-value font :xfont)))
                                 (and (typep f 'runes:font) f)))
          (wl-font-to-internal root-window font))))

(defun wl-font-exists-p (root-window name)
  (declare (ignore root-window))
  (ensure-wl-truetype-initialized)
  (not (null (find (string name) (runes:get-font-families) :test #'string-equal))))

(defun wl-font-name-p (root-window arg)
  (declare (ignore root-window))
  (or (stringp arg) (and (schema-p arg) (is-a-p arg opal::font))))

(defun wl-make-font-name (root-window key)
  (declare (ignore root-window))
  (format nil "~A" key))

(defun wl-delete-font (root-window font)
  "Forget FONT's Runes font; it lives entirely in Lisp."
  (declare (ignore root-window))
  (let ((tt-font (and (schema-p font) (kr:g-cached-value font :xfont))))
    (when tt-font
      (maphash (lambda (key value)
                 (when (eq value tt-font)
                   (remhash key *wl-font-cache-table*)))
               *wl-font-cache-table*)
      (clrhash *wl-layout-cache*)))
  t)

(defun wl-font-max-min-width (root-window font min-too)
  (let* ((tt-font (wl-resolve-font root-window font))
         (max-w (runes:text-line-width *wl-dpi* tt-font "M"))
         (min-w (runes:text-line-width *wl-dpi* tt-font "i")))
    (if min-too (values max-w min-w) max-w)))

(defun wl-max-character-ascent (root-window font)
  (runes:font-ascent *wl-dpi* (wl-resolve-font root-window font)))

(defun wl-max-character-descent (root-window font)
  (abs (runes:font-descent *wl-dpi* (wl-resolve-font root-window font))))

;;; Widths are advance widths (TEXT-LINE-WIDTH), as X font metrics give
;;; them: Opal lays text out by adding up character widths.
(defun wl-character-width (root-window font character)
  (runes:text-line-width *wl-dpi* (wl-resolve-font root-window font)
                            (if character (string (code-char character)) "X")))

(defun wl-text-width (root-window opal-font string)
  (runes:text-line-width *wl-dpi* (wl-resolve-font root-window opal-font) (or string "")))

(defun wl-text-extents (root-window opal-font string)
  (let* ((tt-font (wl-resolve-font root-window opal-font))
         (str (or string ""))
         (width (runes:text-line-width *wl-dpi* tt-font str))
         (ascent (runes:font-ascent *wl-dpi* tt-font))
         (descent (abs (runes:font-descent *wl-dpi* tt-font))))
    (values width ascent descent 0 width width)))

(defun wl-layout (tt-font string &optional (dpi *wl-dpi*))
  (let ((key (list* dpi tt-font string)))
    (or (gethash key *wl-layout-cache*)
        (progn
          (when (> (hash-table-count *wl-layout-cache*) 4000)
            (clrhash *wl-layout-cache*))
          (setf (gethash (list* dpi tt-font (copy-seq string)) *wl-layout-cache*)
                (map 'vector (lambda (entry)
                               (destructuring-bind (index pen image) entry
                                 (declare (ignore index))
                                 (cons (round pen) image)))
                     (runes:layout-glyphs tt-font string dpi dpi)))))))

(defun wl-draw-text (window x y string font function line-style
                     &optional fill-background invert-p)
  (declare (ignore function))
  (let* ((drawable (the-drawable window))
         (s (wl-target drawable))
         (str (string string))
         (tt-font (wl-resolve-font window font))
         (gc (wl-line-gc window)))
    (when (and drawable tt-font (plusp (length str)))
      (let* ((style-fg (if (and line-style (schema-p line-style))
                           (wl-color-to-pixel (g-value line-style :foreground-color) 0)
                           0))
             (style-bg (if (and line-style (schema-p line-style))
                           (wl-color-to-pixel (g-value line-style :background-color) #xFFFFFF)
                           #xFFFFFF))
             (fg (if invert-p style-bg style-fg))
             (k (px-surface-scale s))
             (dpi (* *wl-dpi* k))
             ;; Opal measured the text in logical pixels; it is drawn at
             ;; the surface's scale, from the device baseline.
             (ascent (runes:font-ascent *wl-dpi* tt-font))
             (descent (abs (runes:font-descent *wl-dpi* tt-font)))
             (width (runes:text-line-width *wl-dpi* tt-font str))
             (dx (dev-edge x k)) (dy (dev-edge y k))
             (clip (px-gc-clip (wl-gc-device gc k))))
        (when fill-background
          (multiple-value-bind (bx by bw bh)
              (dev-rect x (- y ascent) (max 1 width) (max 1 (+ ascent descent)) k)
            (px-clear-rectangle-clipped s clip bx by bw bh (if invert-p style-fg style-bg))))
        (loop for (pen . image) across (wl-layout tt-font str dpi)
              when (plusp (runes:glyph-image-width image))
                do (px-blend-alpha s clip
                                   (- (+ dx pen) (runes:glyph-image-x image))
                                   (- dy (runes:glyph-image-y image))
                                   (runes:glyph-image-width image)
                                   (runes:glyph-image-height image)
                                   (runes:glyph-image-data image)
                                   (runes:glyph-image-stride image)
                                   fg))
        (loop for (bx by bw bh) in (runes:font-decorations tt-font str dx dy dpi dpi t)
              do (px-clear-rectangle-clipped s clip bx by bw bh fg))
        (wl-note-drawn drawable (- x 2) (- y ascent 2) (+ width 4) (+ ascent descent 4))))))

(defun px-clear-rectangle-clipped (s clip x y w h pixel)
  (loop for row from (max 0 y) below (min (+ y h) (px-surface-height s))
        do (dolist (iv (px-row-intervals s clip row))
             (let ((a (max x (car iv))) (b (min (+ x w) (cdr iv))))
               (when (< a b)
                 (fill (px-surface-pixels s) pixel
                       :start (+ (* row (px-surface-width s)) a)
                       :end (+ (* row (px-surface-width s)) b)))))))


;;; Images and Pixmaps

(defun wl-pixarray-element-type (depth)
  (cond ((= depth 1) 'bit)
        ((<= depth 8) '(unsigned-byte 8))
        ((<= depth 16) '(unsigned-byte 16))
        (t '(unsigned-byte 32))))

(defun wl-image-into-surface (s image)
  "Put IMAGE, a WL-IMAGE or an array, into the PX-SURFACE S at its origin."
  (let ((data (if (wl-image-p image) (wl-image-data image) image))
        (gc (make-px-gc :function +px-gx-copy+ :foreground 1 :background 0)))
    (when (arrayp data)
      (cond
        ((and (wl-image-p image) (= (wl-image-depth image) 1))
         (when (/= (px-surface-depth s) 1)
           (setf (px-gc-foreground gc) #xFFFFFF (px-gc-background gc) 0))
         (px-put-bitmap s gc 0 0 (wl-image-width image) (wl-image-height image)
                        data (wl-image-bytes-per-line image)))
        ((= (array-rank data) 2)
         (if (= (px-surface-depth s) 1)
             (destructuring-bind (h w) (array-dimensions data)
               (dotimes (y (min h (px-surface-height s)))
                 (dotimes (x (min w (px-surface-width s)))
                   (setf (aref (px-surface-pixels s) (+ (* y (px-surface-width s)) x))
                         (if (zerop (aref data y x)) 0 1)))))
             (px-put-pixels s gc 0 0 data)))))))

(defun wl-create-pixmap (root-window width height depth &optional image bitmap-p data-array)
  (declare (ignore root-window bitmap-p data-array))
  (let ((s (make-px-surface width height :depth (if (eql depth 1) 1 24)
                                         :initial (if (eql depth 1) 0 #xFFFFFF))))
    (when image (wl-image-into-surface s image))
    s))

(defun wl-delete-pixmap (root-window pixmap &optional buffer-too)
  "Pixmaps live in Lisp memory: forget PIXMAP.  With BUFFER-TOO,
ROOT-WINDOW is the window PIXMAP is the double buffer of."
  (remhash pixmap *wl-drawable-to-window-table*)
  (when buffer-too
    (s-value root-window :buffer-gcontext nil)))

(defun wl-build-pixmap (window image width height bitmap-p)
  (wl-create-pixmap window width height 1 image bitmap-p))

(defun wl-copy-to-pixmap (root-window to from width height)
  (declare (ignore root-window width height))
  (when (px-surface-p to)
    (wl-image-into-surface to from)))

(defun wl-create-image (root-window width height depth from-data-p
                        &optional color-or-data properties bits-per-pixel left-pad data-array)
  (declare (ignore root-window left-pad data-array))
  (let* ((bpp (or bits-per-pixel (depth-to-bits-per-pixel depth)))
         (data (if from-data-p
                   color-or-data
                   (make-array (list height width)
                               :element-type (wl-pixarray-element-type bpp)
                               :initial-element (ldb (byte bpp 0)
                                                     (wl-color-to-pixel color-or-data
                                                                        #xFFFFFF))))))
    (make-wl-image :width width :height height :depth depth :bits-per-pixel bpp
                   :bytes-per-line (ceiling (* width bpp) 8)
                   :data data :properties properties
                   :x-hot (getf properties :x-hot 0) :y-hot (getf properties :y-hot 0))))

(defun wl-create-image-array (root-window width height depth)
  (declare (ignore root-window))
  (make-array (list height width) :element-type (wl-pixarray-element-type depth)))

(defun wl-image-size (a-window image)
  (declare (ignore a-window))
  (if (wl-image-p image)
      (values (wl-image-width image) (wl-image-height image) (wl-image-depth image))
      (values 16 16 1)))

(defun wl-image-bit (root-window image x y)
  (declare (ignore root-window))
  (when (wl-image-p image)
    (let ((data (wl-image-data image)))
      (if (= (array-rank data) 2)
          (/= 0 (aref data y x))
          (let ((byte-pos (+ (floor x 8) (* (wl-image-bytes-per-line image) y))))
            (and (< byte-pos (array-total-size data))
                 (logbitp (mod x 8) (row-major-aref data byte-pos))))))))

(defun wl-image-to-array (root-window image)
  (declare (ignore root-window))
  (if (wl-image-p image) (wl-image-data image) image))

(defun wl-image-hot-spot (root-window image)
  (declare (ignore root-window))
  (if (wl-image-p image)
      (values (wl-image-x-hot image) (wl-image-y-hot image))
      (values 0 0)))

(defun wl-get-descriptor (index)
  "Garnet's 4x4 halftone patterns, for indices 0 to 16."
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
    (t  '(#*1111 #*1111 #*1111 #*1111))))

(defun wl-image-from-bit-vectors (bitvecs)
  "A bitmap WL-IMAGE from BITVECS, one bit vector per row, LSB first."
  (let* ((rows (coerce bitvecs 'simple-vector))
         (height (length rows))
         (width (reduce #'max rows :key #'length :initial-value 0))
         (bpl (ceiling width 8))
         (data (make-array (* bpl height) :element-type '(unsigned-byte 8) :initial-element 0)))
    (dotimes (y height)
      (let ((row (svref rows y)))
        (dotimes (x (length row))
          (when (= 1 (bit row x))
            (setf (ldb (byte 1 (mod x 8)) (aref data (+ (* y bpl) (floor x 8)))) 1)))))
    (make-wl-image :width width :height height :depth 1 :bits-per-pixel 1
                   :bytes-per-line bpl :data data)))

(defun wl-device-image (root-window index)
  (declare (ignore root-window))
  (wl-image-from-bit-vectors (wl-get-descriptor index)))

(defun wl-image-from-bits (root-window patterns)
  (declare (ignore root-window))
  (cond
    ((null patterns) nil)
    ((bit-vector-p (first patterns)) (wl-image-from-bit-vectors patterns))
    (t
     (let* ((h (length patterns))
            (arr (make-array (* h 2) :element-type '(unsigned-byte 8))))
       (loop for p in patterns
             for i from 0
             do (setf (aref arr (* i 2)) (logand p #xff)
                      (aref arr (1+ (* i 2))) (ash (logand p #xff00) -8)))
       (make-wl-image :width 16 :height h :depth 1 :bits-per-pixel 1
                      :bytes-per-line 2 :data arr)))))

(defvar *wl-scaled-images* (trivial-garbage:make-weak-hash-table :weakness :key :test 'eq)
  "Image -> (DW DH . the image enlarged to DW by DH), for drawing at a scale.")

(defun wl-image-at-size (image w h dw dh)
  "IMAGE, W by H, enlarged to DW by DH, nearest pixel, kept for next time."
  (let ((cached (gethash image *wl-scaled-images*)))
    (if (and cached (= (first cached) dw) (= (second cached) dh))
        (cddr cached)
        (let* ((data (wl-image-data image))
               (scaled
                 (if (= (wl-image-depth image) 1)
                     (let* ((bpl (ceiling dw 8))
                            (out (make-array (* bpl dh) :element-type '(unsigned-byte 8)
                                                        :initial-element 0)))
                       (dotimes (r dh)
                         (dotimes (c dw)
                           (let ((i (+ (* (floor (* r h) dh) (wl-image-bytes-per-line image))
                                       (floor (floor (* c w) dw) 8))))
                             (when (and (< i (array-total-size data))
                                        (logbitp (mod (floor (* c w) dw) 8)
                                                 (row-major-aref data i)))
                               (setf (ldb (byte 1 (mod c 8)) (aref out (+ (* r bpl) (floor c 8))))
                                     1)))))
                       (make-wl-image :width dw :height dh :depth 1 :bits-per-pixel 1
                                      :bytes-per-line bpl :data out))
                     (let ((out (make-array (list dh dw) :element-type '(unsigned-byte 32))))
                       (dotimes (r dh)
                         (dotimes (c dw)
                           (setf (aref out r c)
                                 (or (aref data (min (1- (array-dimension data 0)) (floor (* r h) dh))
                                           (min (1- (array-dimension data 1)) (floor (* c w) dw)))
                                     0))))
                       (make-wl-image :width dw :height dh :depth (wl-image-depth image)
                                      :bits-per-pixel 32 :bytes-per-line (* 4 dw) :data out)))))
          (setf (gethash image *wl-scaled-images*) (list* dw dh scaled))
          scaled))))

(defun wl-draw-image (window left top width height image function fill-style)
  (let* ((drawable (the-drawable window))
         (s (wl-target drawable))
         (k (px-surface-scale s))
         (data (if (wl-image-p image) (wl-image-data image) image)))
    (when (and drawable fill-style (arrayp data))
      (let ((gc (wl-gc-device (wl-fill-gc window) k)))
        (set-wl-filling-style gc fill-style nil function)
        (multiple-value-bind (dx dy dw dh) (dev-rect left top width height k)
          (let ((image (if (and (/= k 1) (wl-image-p image)
                                (or (= (wl-image-depth image) 1) (= (array-rank data) 2)))
                           (wl-image-at-size image width height dw dh)
                           image)))
            (if (and (wl-image-p image) (= (wl-image-depth image) 1))
                (px-put-bitmap s gc dx dy (wl-image-width image) (wl-image-height image)
                               (wl-image-data image) (wl-image-bytes-per-line image))
                (let ((data (if (wl-image-p image) (wl-image-data image) image)))
                  (when (= (array-rank data) 2)
                    (px-put-pixels s gc dx dy data))))))
        (wl-note-drawn drawable left top width height)))))

(defun wl-window-to-image (window left top width height)
  "A WL-IMAGE of a region of WINDOW, with a (HEIGHT WIDTH) pixel array."
  (let ((s (wl-target (the-drawable window))))
    (when s
      (let* ((w (max 1 (round (or width (g-value window :width) 1))))
             (h (max 1 (round (or height (g-value window :height) 1))))
             (x (round (or left 0))) (y (round (or top 0)))
             (arr (make-array (list h w) :element-type '(unsigned-byte 32) :initial-element 0)))
        ;; One device pixel for each logical one, at its centre.
        (dotimes (r h)
          (dotimes (c w)
            (let ((sx (dev-centre-i (+ x c) (px-surface-scale s)))
                  (sy (dev-centre-i (+ y r) (px-surface-scale s))))
              (when (and (< -1 sx (px-surface-width s)) (< -1 sy (px-surface-height s)))
                (setf (aref arr r c)
                      (aref (px-surface-pixels s) (+ (* sy (px-surface-width s)) sx)))))))
        (make-wl-image :width w :height h :depth 24 :bits-per-pixel 32
                       :bytes-per-line (* 4 w) :data arr)))))

(defun wl-stippled-p (root-window)
  (declare (ignore root-window))
  (and *wl-fill-gc* (eq (px-gc-fill-style *wl-fill-gc*) :stippled)))

(defun wl-read-an-image (root-window pathname)
  "Read an X11 bitmap (.xbm) file from PATHNAME as a WL-IMAGE."
  (declare (ignore root-window))
  (with-open-file (stream pathname :direction :input :if-does-not-exist nil)
    (unless stream
      (return-from wl-read-an-image nil))
    (let (width height x-hot y-hot (bytes nil) (in-data nil))
      (flet ((value (line)
               (parse-integer (car (last (uiop:split-string line :separator '(#\Space #\Tab))))
                              :junk-allowed t)))
        (loop for line = (read-line stream nil nil)
              while line
              do (cond
                   (in-data nil)
                   ((search "_width" line) (setf width (value line)))
                   ((search "_height" line) (setf height (value line)))
                   ((search "_x_hot" line) (setf x-hot (value line)))
                   ((search "_y_hot" line) (setf y-hot (value line)))
                   ((search "static" line) (setf in-data t)))
                 (when in-data
                   (dolist (tok (uiop:split-string line :separator '(#\Space #\Tab #\, #\{ #\} #\;)))
                     (when (and (> (length tok) 2) (string-equal (subseq tok 0 2) "0x"))
                       (push (or (parse-integer tok :start 2 :radix 16 :junk-allowed t) 0)
                             bytes))))))
      (when (and width height bytes)
        (make-wl-image :width width :height height :depth 1 :bits-per-pixel 1
                       :bytes-per-line (ceiling width 8)
                       :data (make-array (length bytes) :element-type '(unsigned-byte 8)
                                                        :initial-contents (nreverse bytes))
                       :x-hot x-hot :y-hot y-hot)))))

(defun wl-write-an-image (root-window pathname image)
  "Write a bitmap WL-IMAGE to PATHNAME in X11 bitmap (.xbm) format."
  (declare (ignore root-window))
  (when (wl-image-p image)
    (with-open-file (stream pathname :direction :output
                                     :if-exists :supersede :if-does-not-exist :create)
      (let ((name (pathname-name pathname))
            (data (wl-image-data image)))
        (format stream "#define ~A_width ~D~%" name (wl-image-width image))
        (format stream "#define ~A_height ~D~%" name (wl-image-height image))
        (when (wl-image-x-hot image)
          (format stream "#define ~A_x_hot ~D~%" name (wl-image-x-hot image)))
        (when (wl-image-y-hot image)
          (format stream "#define ~A_y_hot ~D~%" name (wl-image-y-hot image)))
        (format stream "static unsigned char ~A_bits[] = {~%" name)
        (let ((total (array-total-size data)))
          (dotimes (i total)
            (format stream " 0x~2,'0X~:[~;,~]~:[~;~%~]"
                    (row-major-aref data i) (< i (1- total)) (zerop (mod (1+ i) 12)))))
        (format stream "};~%"))
      t)))


;;; Input: pointer

;;; X11 modifier and button state bits, which Garnet's interactors expect.
(defconstant +wl-shift-mask+ 1)
(defconstant +wl-lock-mask+ 2)
(defconstant +wl-control-mask+ 4)
(defconstant +wl-mod1-mask+ 8)
(defconstant +wl-mod2-mask+ 16)
(defconstant +wl-mod4-mask+ 64)
(defconstant +wl-button1-mask+ 256)

(defvar *wl-pointer-x* 0 "Pointer position in *WL-POINTER-WINDOW*.")
(defvar *wl-pointer-y* 0)
(defvar *wl-pointer-serial* 0 "The serial of the pointer's last enter.")
(defvar *wl-current-cursor* nil "The cursor last set: a WL-CURSOR or a shape.")
(defvar *wl-input-serial* 0
  "The serial of the last input event, which setting the clipboard needs.")
(defvar *wl-buttons-down* 0 "X button state bits of the buttons held down.")
(defvar *wl-implicit-grab* nil
  "The window a button was pressed in, which gets the pointer's events
until every button is released, as X's implicit grab does.")
(defvar *wl-under-pointer* nil "The deepest window last under the pointer.")
(defvar *wl-axis-accumulator* 0)

(defun wl-modifier-state ()
  "The X11 state bits for the modifiers held and the buttons down."
  (logior *wl-buttons-down*
          (if (wl-null-pointer-p *wl-xkb-state*)
              0
              (flet ((on (name bit)
                       (if (plusp (xkb:xkb-state-mod-name-is-active
                                   *wl-xkb-state* name '(:mods-effective)))
                           bit 0)))
                (logior (on "Shift" +wl-shift-mask+)
                        (on "Lock" +wl-lock-mask+)
                        (on "Control" +wl-control-mask+)
                        (on "Mod1" +wl-mod1-mask+)
                        (on "Mod2" +wl-mod2-mask+)
                        (on "Mod4" +wl-mod4-mask+))))))

(defun wl-deepest-window (win x y)
  "The deepest mapped window at (X, Y) of WIN, and the point in it."
  (loop for child in (reverse (wl-window-children win))
        when (and (wl-window-mapped child)
                  (<= (wl-window-x child) x)
                  (< x (+ (wl-window-x child) (wl-window-width child)))
                  (<= (wl-window-y child) y)
                  (< y (+ (wl-window-y child) (wl-window-height child))))
          do (return-from wl-deepest-window
               (wl-deepest-window child (- x (wl-window-x child)) (- y (wl-window-y child)))))
  (values win x y))

(defun wl-mask-wants (win what)
  "Whether WIN's event mask selects WHAT: :MOTION or :CROSSING (enter and
leave).  Opal sets masks by name (:E-K-M, :K-M, :E-K, :K) or as X bits."
  (let ((mask (wl-window-event-mask win)))
    (cond ((eq mask :default) nil)
          ((integerp mask)
           (logtest mask (if (eq what :motion) 64 (logior 16 32))))
          ((symbolp mask)
           (find (if (eq what :motion) #\M #\E) (symbol-name mask)))
          (t nil))))

(defun wl-pointer-target (what)
  "The window a pointer event of kind WHAT (:BUTTON, :MOTION) goes to, and
the pointer's position in it; NIL if none does."
  (let ((top *wl-pointer-window*))
    (when top
      (let ((grab (or *wl-grab* *wl-implicit-grab*)))
        (if grab
            ;; Grabbed: the grabbing window gets the event, at the pointer's
            ;; position relative to it.
            (multiple-value-bind (tx ty) (wl-screen-origin top)
              (multiple-value-bind (gx gy) (wl-screen-origin grab)
                (when (or (eq what :button) (eq grab *wl-implicit-grab*)
                          (wl-mask-wants grab :motion))
                  (values grab (- (+ tx *wl-pointer-x*) gx) (- (+ ty *wl-pointer-y*) gy)))))
            (multiple-value-bind (win x y) (wl-deepest-window top *wl-pointer-x* *wl-pointer-y*)
              ;; As X propagates events up to the first window that
              ;; selected them.
              (if (eq what :motion)
                  (loop for w = win then (wl-window-parent w)
                        while (and w (not (eq (wl-window-kind w) :root)))
                        when (wl-mask-wants w :motion)
                          do (return (values w x y))
                        do (incf x (wl-window-x w))
                           (incf y (wl-window-y w)))
                  (values win x y))))))))

(defun wl-update-crossing (time)
  "Send leave and enter events if the deepest window under the pointer changed."
  (let ((now (and *wl-pointer-window*
                  (wl-deepest-window *wl-pointer-window* *wl-pointer-x* *wl-pointer-y*))))
    (unless (eq now *wl-under-pointer*)
      (let ((old *wl-under-pointer*))
        (setf *wl-under-pointer* now)
        (when (and old (wl-mask-wants old :crossing))
          (wl-queue-event (list :leave-notify old 0 0 time)))
        (when (and now (wl-mask-wants now :crossing))
          (multiple-value-bind (win x y)
              (wl-deepest-window *wl-pointer-window* *wl-pointer-x* *wl-pointer-y*)
            (wl-queue-event (list :enter-notify win x y time))))))))

(defun wl-evdev-button (button)
  "The X button for the evdev BUTTON code."
  (case button
    (#x110 1)                           ; BTN_LEFT
    (#x111 3)                           ; BTN_RIGHT
    (#x112 2)                           ; BTN_MIDDLE
    (t (+ 8 (- button #x113)))))

(defun wl-queue-button (x-button pressp time)
  (multiple-value-bind (win x y) (wl-pointer-target :button)
    (when win
      (wl-queue-event (list (if pressp :button-press :button-release)
                            win x y (wl-modifier-state) x-button time)))))

(defun wl-handle-pointer (&rest event)
  (event-case event
    (:enter (serial surface sx sy)
     (setf *wl-pointer-serial* serial
           *wl-input-serial* serial
           *wl-current-cursor* nil
           *wl-pointer-window* (and surface (gethash surface *wl-surface-to-window*))
           *wl-pointer-x* (floor sx) *wl-pointer-y* (floor sy))
     (when *wl-pointer-window*
       (unless (eq (wl-window-kind *wl-pointer-window*) :popup)
         (setf *wl-last-toplevel* *wl-pointer-window*)))
     (wl-update-crossing 0)
     (wl-update-cursor))
    (:leave (serial surface)
     (declare (ignore serial surface))
     (setf *wl-pointer-window* nil)
     (wl-update-crossing 0))
    (:motion (time sx sy)
     (setf *wl-pointer-x* (floor sx) *wl-pointer-y* (floor sy))
     (wl-update-crossing time)
     (wl-update-cursor)
     (multiple-value-bind (win x y) (wl-pointer-target :motion)
       (when win
         (wl-queue-event (list :motion-notify win x y time)))))
    (:button (serial time button state)
     (setf *wl-input-serial* serial)
     (let* ((x-button (wl-evdev-button button))
            (pressp (eq state :pressed))
            (bit (if (<= 1 x-button 5) (ash +wl-button1-mask+ (1- x-button)) 0)))
       (when (and pressp (zerop *wl-buttons-down*))
         (setf *wl-implicit-grab* (and *wl-pointer-window*
                                       (wl-deepest-window *wl-pointer-window*
                                                          *wl-pointer-x* *wl-pointer-y*))))
       ;; X reports the state before the event.
       (wl-queue-button x-button pressp time)
       (setf *wl-buttons-down* (if pressp
                                   (logior *wl-buttons-down* bit)
                                   (logandc2 *wl-buttons-down* bit)))
       (when (zerop *wl-buttons-down*)
         (setf *wl-implicit-grab* nil))))
    (:axis (time axis value)
     ;; A wheel notch scrolls 10 units (15 on some compositors); report one
     ;; X button 4 or 5 click for each 10.
     (when (eq axis :vertical-scroll)
       (incf *wl-axis-accumulator* value)
       (loop while (>= (abs *wl-axis-accumulator*) 10)
             do (let ((b (if (minusp *wl-axis-accumulator*) 4 5)))
                  (wl-queue-button b t time)
                  (wl-queue-button b nil time)
                  (decf *wl-axis-accumulator* (if (= b 4) -10 10))))))))

;;; The pointer image.  Opal's cursors are bitmaps (its arrow, hourglass
;;; and others), drawn here into cursor surfaces just as Opal made them,
;;; or glyphs of X's cursor font, which have no Wayland counterpart: those
;;; are asked of the compositor by name, through cursor-shape-v1, as the
;;; nearest shape of its cursor theme.  Without cursor-shape-v1, they are
;;; shown as Garnet's arrow.

(defstruct wl-cursor
  (width 0) (height 0)
  pixels                                ; ARGB, a (WIDTH * HEIGHT) vector
  (x-hot 0) (y-hot 0)
  surface buffer)                       ; made when first shown

(defparameter *wl-arrow-cursor*
  '("X"
    "XX"
    "X.X"
    "X..X"
    "X...X"
    "X....X"
    "X.....X"
    "X......X"
    "X.......X"
    "X........X"
    "X.....XXXXX"
    "X..X..X"
    "X.X X..X"
    "XX  X..X"
    "X    X..X"
    "     X..X"
    "      XX")
  "The cursor for windows with none, and for cursor font glyphs when the
compositor cannot show them by name.")

(defvar *wl-default-cursor*
  (let* ((w 16) (h (length *wl-arrow-cursor*))
         (pixels (make-array (* w h) :element-type '(unsigned-byte 32) :initial-element 0)))
    (loop for row in *wl-arrow-cursor*
          for y from 0
          do (loop for c across row
                   for x from 0
                   do (setf (aref pixels (+ (* y w) x))
                            (case c (#\X #xFF000000) (#\. #xFFFFFFFF) (t 0)))))
    (make-wl-cursor :width w :height h :pixels pixels)))

;;; X cursor font glyph -> cursor-shape-v1 shape (X11's cursorfont.h).
(defparameter *wl-cursor-font-shapes*
  '((0 . :not-allowed) (2 . :default) (12 . :sw-resize) (14 . :se-resize)
    (16 . :s-resize) (26 . :wait) (30 . :crosshair) (34 . :crosshair)
    (42 . :ew-resize) (52 . :move) (58 . :pointer) (60 . :pointer)
    (68 . :default) (70 . :w-resize) (86 . :crosshair) (88 . :not-allowed)
    (90 . :crosshair) (92 . :help) (94 . :default) (96 . :e-resize)
    (108 . :ew-resize) (116 . :ns-resize) (120 . :all-scroll) (128 . :crosshair)
    (130 . :crosshair) (132 . :default) (134 . :nw-resize) (136 . :ne-resize)
    (138 . :n-resize) (150 . :wait) (152 . :text)))

(defun wl-cursor-from-bitmaps (source mask foreground background x-hot y-hot)
  "A WL-CURSOR from the depth-1 PX-SURFACEs SOURCE and MASK: where the mask
is set, the source's 1s in FOREGROUND and 0s in BACKGROUND, as X makes a
cursor from pixmaps.  Without a mask, all of it is shown."
  (let* ((w (px-surface-width source)) (h (px-surface-height source))
         (pixels (make-array (* w h) :element-type '(unsigned-byte 32) :initial-element 0)))
    (dotimes (y h)
      (dotimes (x w)
        (let ((on (/= 0 (aref (px-surface-pixels source) (+ (* y w) x))))
              (shown (or (null mask)
                         (and (< x (px-surface-width mask)) (< y (px-surface-height mask))
                              (/= 0 (aref (px-surface-pixels mask)
                                          (+ (* y (px-surface-width mask)) x)))))))
          (when shown
            (setf (aref pixels (+ (* y w) x))
                  (logior #xFF000000 (if on foreground background)))))))
    (make-wl-cursor :width w :height h :pixels pixels :x-hot x-hot :y-hot y-hot)))

(defun wl-show-cursor-surface (cursor)
  "CURSOR's wl_surface, made and filled the first time it is shown."
  (or (wl-cursor-surface cursor)
      (let* ((w (wl-cursor-width cursor)) (h (wl-cursor-height cursor))
             (size (* 4 w h)))
        (multiple-value-bind (fd ptr) (wl-make-shm size)
          (cffi:with-pointer-to-vector-data (p (wl-cursor-pixels cursor))
            (%wl-memcpy ptr p size))
          (let* ((pool (wl-shm.create-pool *wl-shm* fd size))
                 (buffer (wl-shm-pool.create-buffer pool 0 w h (* 4 w) :argb8888))
                 (surface (wl-compositor.create-surface *wl-compositor*)))
            (destroy-proxy pool)
            ;; The compositor has its own mapping of the memory now.
            (%wl-munmap ptr size)
            (%wl-close fd)
            (wl-surface.attach surface buffer 0 0)
            (wl-surface.damage-buffer surface 0 0 w h)
            (wl-surface.commit surface)
            (setf (wl-cursor-buffer cursor) buffer
                  (wl-cursor-surface cursor) surface))))))

(defun wl-window-cursor-under-pointer ()
  "The cursor of the deepest window under the pointer, or of its nearest
ancestor that has one."
  (when *wl-pointer-window*
    (loop for w = (wl-deepest-window *wl-pointer-window* *wl-pointer-x* *wl-pointer-y*)
            then (wl-window-parent w)
          while (and w (not (eq (wl-window-kind w) :root)))
          when (wl-window-cursor w) do (return (wl-window-cursor w)))))

(defun wl-update-cursor ()
  "Show the cursor for where the pointer is, if it is not shown already."
  (when *wl-pointer*
    (let ((cursor (or (wl-window-cursor-under-pointer) *wl-default-cursor*)))
      (when (and (keywordp cursor) (null *wl-cursor-shape-device*))
        (setf cursor *wl-default-cursor*))
      (unless (eq cursor *wl-current-cursor*)
        (setf *wl-current-cursor* cursor)
        (if (keywordp cursor)
            (garnet-wl-protocols:wp-cursor-shape-device-v1.set-shape
             *wl-cursor-shape-device* *wl-pointer-serial* cursor)
            (wl-pointer.set-cursor *wl-pointer* *wl-pointer-serial*
                                   (wl-show-cursor-surface cursor)
                                   (wl-cursor-x-hot cursor) (wl-cursor-y-hot cursor)))))))


;;; Input: keyboard

(defvar *wl-keysym-of-code* (make-hash-table)
  "Keycode -> the keysym it gave when last pressed, for WL-TRANSLATE-CODE.")
(defvar *wl-repeat-rate* 25 "Key repeats per second; 0 for none.")
(defvar *wl-repeat-delay* 600 "Milliseconds before a held key repeats.")
(defvar *wl-repeat* nil
  "The key repeating: (KEYCODE NEXT-TIME-MS TIME), or NIL.")

(defun wl-now-ms ()
  (floor (* 1000 (get-internal-real-time)) internal-time-units-per-second))

(defun wl-load-keymap (fd size)
  (let ((ptr (%wl-mmap (cffi:null-pointer) size +wl-prot-read+ +wl-map-private+ fd 0)))
    (unwind-protect
         (unless (wl-map-failed-p ptr)
           (unwind-protect
                (let ((keymap (xkb:xkb-keymap-new-from-string *wl-xkb-context* ptr :text-v1 ())))
                  (unless (wl-null-pointer-p keymap)
                    (unless (wl-null-pointer-p *wl-xkb-state*)
                      (xkb:xkb-state-unref *wl-xkb-state*))
                    (unless (wl-null-pointer-p *wl-xkb-keymap*)
                      (xkb:xkb-keymap-unref *wl-xkb-keymap*))
                    (setf *wl-xkb-keymap* keymap
                          *wl-xkb-state* (xkb:xkb-state-new keymap))))
             (%wl-munmap ptr size)))
      (%wl-close fd))))

(defun wl-keyboard-target ()
  "The window key events go to: the deepest one under the pointer, if it is
in the focused window, else the focused window."
  (let ((focus *wl-focus-window*))
    (when focus
      (if (eq *wl-pointer-window* focus)
          (multiple-value-bind (win x y)
              (wl-deepest-window focus *wl-pointer-x* *wl-pointer-y*)
            (values win x y))
          (values focus 0 0)))))

(defun wl-queue-key (keycode time)
  (unless (wl-null-pointer-p *wl-xkb-state*)
    (setf (gethash keycode *wl-keysym-of-code*)
          (xkb:xkb-state-key-get-one-sym *wl-xkb-state* keycode))
    (multiple-value-bind (win x y) (wl-keyboard-target)
      (when win
        (wl-queue-event (list :key-press win x y (wl-modifier-state) keycode time))))))

(defun wl-handle-keyboard (&rest event)
  (event-case event
    (:keymap (format fd size)
     (if (eq format :xkb-v1)
         (wl-load-keymap fd size)
         (%wl-close fd)))
    (:enter (serial surface keys)
     (declare (ignore keys))
     (setf *wl-input-serial* serial)
     (setf *wl-focus-window* (and surface (gethash surface *wl-surface-to-window*))))
    (:leave (serial surface)
     (declare (ignore serial surface))
     (setf *wl-focus-window* nil
           *wl-repeat* nil))
    (:modifiers (serial depressed latched locked group)
     (declare (ignore serial))
     (unless (wl-null-pointer-p *wl-xkb-state*)
       (xkb:xkb-state-update-mask *wl-xkb-state* depressed latched locked 0 0 group)))
    (:key (serial time key state)
     (setf *wl-input-serial* serial)
     (let ((keycode (+ key 8)))
       (if (eq state :pressed)
           (progn
             (wl-queue-key keycode time)
             (setf *wl-repeat*
                   (and (plusp *wl-repeat-rate*)
                        (not (wl-null-pointer-p *wl-xkb-keymap*))
                        (plusp (xkb:xkb-keymap-key-repeats *wl-xkb-keymap* keycode))
                        (list keycode (+ (wl-now-ms) *wl-repeat-delay*) time))))
           (when (and *wl-repeat* (= keycode (first *wl-repeat*)))
             (setf *wl-repeat* nil)))))
    (:repeat-info (rate delay)
     (setf *wl-repeat-rate* rate *wl-repeat-delay* delay))))

(defun wl-repeat-timeout ()
  "Milliseconds until the held key next repeats, or NIL."
  (and *wl-repeat* (max 0 (- (second *wl-repeat*) (wl-now-ms)))))

(defun wl-run-repeat ()
  (when (and *wl-repeat* (<= (second *wl-repeat*) (wl-now-ms)))
    (destructuring-bind (keycode next time) *wl-repeat*
      (wl-queue-key keycode time)
      (setf *wl-repeat* (list keycode (+ next (floor 1000 (max 1 *wl-repeat-rate*))) time)))))

(defun wl-translate-code (window scan-code shiftp)
  "The keysym SCAN-CODE gave when pressed: XKB has applied the modifiers."
  (declare (ignore window shiftp))
  (gethash scan-code *wl-keysym-of-code* 0))


;;; Events, Cut Buffer & Interactors

(defparameter *last-state* nil)
(defparameter *last-code* nil)
(declaim (integer *last-time*))
(defparameter *last-time* 0)

(defun wl-check-double-press (root-window state code time)
  (declare (ignore root-window) (integer time))
  (if inter::*double-click-time*
      (let ((newcode (if (and (eq state *last-state*)
                              (eq code *last-code*)
                              (<= (- time *last-time*) inter::*double-click-time*))
                         (+ code inter::*double-offset*)
                         code)))
        (setf *last-state* state *last-code* code *last-time* time)
        newcode)
      code))

(defun wl-set-interest-in-moved (window interestedp)
  (let ((drawable (g-value window :drawable)))
    (if drawable
        (if interestedp
            (let* ((want-enter-leave (g-value window :want-enter-leave-events))
                   (em (if want-enter-leave :E-K-M :K-M)))
              (gem:mouse-grab window t want-enter-leave :CHANGE)
              (gem:set-window-property window :EVENT-MASK em)
              (s-value window :event-mask em))
            (let ((em (or (g-value window :ignore-motion-em)
                          (if (g-value window :want-enter-leave-events) :E-K :K))))
              (gem:set-window-property window :EVENT-MASK em)
              (s-value window :event-mask em)))
        (s-value window :want-running-em interestedp))))

(defun wl-translate-mouse-character (root-window button-code modifier-bits event-key)
  (declare (ignore root-window))
  (case event-key
    (:button-release
     (aref inter::*mouse-up-translations* button-code (inter::modifier-index modifier-bits)))
    (:button-press
     (aref inter::*mouse-down-translations* button-code (inter::modifier-index modifier-bits)))))

(defun wl-translate-character (window x y bits scan-code time)
  "The Lisp character for SCAN-CODE with the modifier BITS."
  (declare (ignore x y time))
  (let* ((keysym (gem:translate-code window scan-code nil))
         (temp-char (gethash keysym inter::*keysym-translations*)))
    (if (null temp-char)
        (if (<= #xffe1 keysym #xffee)    ; Shift_L .. Hyper_R: modifier keys
            nil
            (unless inter::*ignore-undefined-keys*
              (error "Undefined keysym ~S, describe Inter:DEFINE-KEYSYM." keysym)))
        (inter::base-char-to-character temp-char bits))))

(defun wl-create-cursor (root-window source mask foreground background from-font-p x y)
  "A cursor for :CURSOR: with FROM-FONT-P, X is a glyph of X's cursor font,
returned as the nearest cursor-shape-v1 shape; otherwise SOURCE and MASK
are depth-1 pixmaps and (X, Y) the hot spot, made into a WL-CURSOR."
  (declare (ignore root-window))
  (flet ((pixel (color default)
           (cond ((and (consp color) (= (length color) 3))
                  ;; 16-bit red, green and blue.
                  (logior (ash (ash (first color) -8) 16) (ash (ash (second color) -8) 8)
                          (ash (third color) -8)))
                 ((and color (schema-p color)) (wl-color-to-pixel color default))
                 (t default))))
    (if from-font-p
        (or (cdr (assoc x *wl-cursor-font-shapes*)) :default)
        (if (px-surface-p source)
            (wl-cursor-from-bitmaps source (and (px-surface-p mask) mask)
                                    (pixel foreground 0) (pixel background #xFFFFFF)
                                    (or x 0) (or y 0))
            *wl-default-cursor*))))

(defun wl-create-state-mask (root-window modifier)
  (if (listp modifier)
      (reduce #'logior (mapcar (lambda (m) (wl-create-state-mask root-window m)) modifier)
              :initial-value 0)
      (case modifier
        (:shift 1) (:lock 2) (:control 4)
        (:mod-1 8) (:mod-2 16) (:mod-3 32) (:mod-4 64) (:mod-5 128)
        (:button-1 256) (:button-2 512) (:button-3 1024)
        (:button-4 2048) (:button-5 4096)
        (t (if (numberp modifier) modifier 0)))))

;;; The cut buffer is the Wayland clipboard (the selection), through
;;; wl_data_device: Garnet's cut text can be pasted in other programs, and
;;; theirs in Garnet.  *WL-CUT-BUFFER* keeps Garnet's own, for when there
;;; is no data device, and to be read back without asking the compositor.

(defvar *wl-cut-buffer* "")
(defvar *wl-selection-source* nil "Our wl_data_source, while it is the selection.")
(defvar *wl-selection-offer* nil "The selection another client offers, if any.")
(defvar *wl-offer-types* (make-hash-table :test 'eq)
  "wl_data_offer -> the MIME types it offers.")

(defparameter *wl-text-types*
  '("text/plain;charset=utf-8" "UTF8_STRING" "text/plain" "TEXT" "STRING"))

(defun wl-forget-offer (offer)
  (when offer
    (remhash offer *wl-offer-types*)
    (unless (typep offer 'wl-destroyed-proxy)
      (destroy-proxy offer))))

(defun wl-handle-data-device (&rest event)
  (event-case event
    (:data-offer (offer)
     (setf (gethash offer *wl-offer-types*) '())
     (push (evlambda
             (:offer (mime-type)
              (push mime-type (gethash offer *wl-offer-types*))))
           (wl-proxy-hooks offer)))
    (:selection (offer)
     (unless (eq offer *wl-selection-offer*)
       (wl-forget-offer *wl-selection-offer*))
     (setf *wl-selection-offer* offer))
    ;; Drag and drop is not supported: let its offers go.
    (:enter (serial surface x y offer)
     (declare (ignore serial surface x y))
     (unless (eq offer *wl-selection-offer*) (wl-forget-offer offer)))))

(defun wl-write-fully (fd octets)
  (cffi:with-pointer-to-vector-data (p octets)
    (let ((done 0) (n (length octets)))
      (loop while (< done n)
            do (let ((w (%wl-write fd (cffi:inc-pointer p done) (- n done))))
                 (if (plusp w) (incf done w) (return)))))))

(defun wl-get-cut-buffer (root-window)
  (declare (ignore root-window))
  (let* ((offer *wl-selection-offer*)
         (type (and offer (not *wl-selection-source*)
                    (find-if (lambda (type) (member type (gethash offer *wl-offer-types*)
                                                    :test #'string=))
                             *wl-text-types*))))
    (or (and type (wl-receive-offer offer type))
        *wl-cut-buffer*)))

(defun wl-receive-offer (offer type)
  "The text OFFER gives as TYPE, read through a pipe, waiting a second at
most for the other client; NIL if it gives none."
  (cffi:with-foreign-object (fds :int 2)
    (when (zerop (%wl-pipe fds))
      (let ((r (cffi:mem-aref fds :int 0)) (w (cffi:mem-aref fds :int 1))
            (octets (make-array 0 :element-type '(unsigned-byte 8)
                                  :adjustable t :fill-pointer 0)))
        (unwind-protect
             (progn
               (wl-data-offer.receive offer type w)
               ;; The request has gone, with its copy of the descriptor.
               (%wl-close w)
               (setf w nil)
               (cffi:with-foreign-object (buf :uint8 4096)
                 (loop while (wl-poll-fds (list r) 1000)
                       do (let ((n (%wl-read r buf 4096)))
                            (if (plusp n)
                                (dotimes (i n)
                                  (vector-push-extend (cffi:mem-aref buf :uint8 i) octets))
                                (return)))))
               (and (plusp (length octets))
                    (babel:octets-to-string (coerce octets '(simple-array (unsigned-byte 8) (*)))
                                            :encoding :utf-8 :errorp nil)))
          (when w (%wl-close w))
          (%wl-close r))))))

(defun wl-set-cut-buffer (root-window string)
  (declare (ignore root-window))
  (when (stringp string)
    (setf *wl-cut-buffer* (copy-seq string))
    (when *wl-data-device*
      (let ((source (wl-data-device-manager.create-data-source *wl-data-device-manager*))
            (octets (babel:string-to-octets string :encoding :utf-8)))
        (dolist (type *wl-text-types*)
          (wl-data-source.offer source type))
        (push (evlambda
                (:send (mime-type fd)
                 (declare (ignore mime-type))
                 (unwind-protect (wl-write-fully fd octets)
                   (%wl-close fd)))
                (:cancelled ()
                 (when (eq *wl-selection-source* source)
                   (setf *wl-selection-source* nil))
                 (destroy-proxy source)))
              (wl-proxy-hooks source))
        (wl-data-device.set-selection *wl-data-device* source *wl-input-serial*)
        (let ((old *wl-selection-source*))
          (setf *wl-selection-source* source)
          (when old (destroy-proxy old))))))
  nil)

(defun wl-socket-fd ()
  ;; Wayflan does not export the socket's file descriptor.
  (slot-value (xyz.shunter.wayflan.client::%wl-display-socket *wl-display*)
              'xyz.shunter.wayflan.wire::%fd))

(defun wl-dispatch-one ()
  "Read and dispatch one Wayland event, as WL-DISPLAY-DISPATCH-EVENT does,
but drop an event sent to, or naming, an object this client has already
destroyed: the compositor may have sent it before it saw the destroy
request.  libwayland ignores such events too; Wayflan signals an error."
  (let ((display *wl-display*))
    (xyz.shunter.wayflan.wire:with-incoming-message
        ((xyz.shunter.wayflan.client::%wl-display-socket display) sender-id opcode buffer)
      (flet ((skip ()
               ;; Mark the message read: it was taken off the socket whole.
               (xyz.shunter.wayflan.wire::incf-buf
                buffer (- (xyz.shunter.wayflan.wire::buf-size buffer)
                          (xyz.shunter.wayflan.wire::buf-offset buffer)))))
        (let ((sender (find-proxy display sender-id)))
          (if (or (null sender) (typep sender 'wl-destroyed-proxy))
              (skip)
              (let ((event (handler-case
                               (xyz.shunter.wayflan.client::%read-event sender opcode buffer)
                             (type-error (e)
                               (unless (typep (type-error-datum e) 'wl-destroyed-proxy)
                                 (error e))
                               (skip)
                               nil))))
                (when event
                  (xyz.shunter.wayflan.client::%dispatch-event sender event)))))))))

(defun wl-read-events ()
  "Dispatch the Wayland events that have arrived, without waiting."
  (loop while (wl-display-listen *wl-display*)
        do (wl-dispatch-one)))

(defun wl-wait (timeout-ms)
  "Wait for the compositor, a timer thread or TIMEOUT-MS milliseconds (NIL:
forever, but no longer than the next key repeat), then dispatch what came."
  (let* ((repeat (wl-repeat-timeout))
         (timeout (cond ((and timeout-ms repeat) (min timeout-ms repeat))
                        (t (or timeout-ms repeat))))
         (ready (wl-poll-fds (list (wl-socket-fd) *wl-wake-read-fd*) timeout)))
    (when (member *wl-wake-read-fd* ready)
      (wl-drain-pipe *wl-wake-read-fd*))
    (wl-read-events)
    (wl-run-repeat)))

(defun wl-discard-mouse-moved-events (root-window)
  (declare (ignore root-window))
  (wl-read-events)
  (let (last)
    (bt:with-lock-held (*wl-event-lock*)
      (loop while (and *wl-event-queue* (eq (first (first *wl-event-queue*)) :motion-notify))
            do (setf last (pop *wl-event-queue*))))
    (if last
        (destructuring-bind (win x y time) (rest last)
          (declare (ignore time))
          (values x y (wl-window-from-drawable nil win)))
        (values nil nil nil))))

(defun wl-discard-pending-events (root-window &optional (timeout 0))
  (declare (ignore root-window))
  (when *wl-display*
    (wl-present-all)
    (wl-read-events)
    (wl-clear-event-queue)
    (when (and timeout (> timeout 0))
      (wl-wait (* 1000 timeout))
      (wl-clear-event-queue)))
  t)

(defun wl-inject-event (window index)
  "Queue a TIMER_EVENT carrying INDEX for WINDOW.  Called from timer
threads; the main loop is woken through the pipe."
  (let ((drawable (g-value window :drawable)))
    (when drawable
      (wl-queue-event (list :client-message drawable :timer_event
                            (make-array 5 :element-type '(unsigned-byte 32)
                                          :initial-contents (list index 0 0 0 0))
                            32))
      (wl-poke-pipe *wl-wake-write-fd*))))

(defun wl-dispatch-event (event ignore-keys)
  (let ((window-of (lambda (d) (wl-window-from-drawable nil d))))
    (destructuring-bind (kind &rest args) event
      (case kind
        (:key-press
         (destructuring-bind (win x y state code time) args
           (if ignore-keys
               (let ((c (wl-translate-character *root-window* 0 0 state code 0)))
                 (when (eq c interactors::*garnet-break-key*)
                   (format t "~%**Aborting transcript due to user command**~%")
                   (return-from wl-dispatch-event :abort)))
               (let ((w (funcall window-of win)))
                 (when w (interactors::do-key-press w x y state code time))))))
        ((:button-press :button-release)
         (unless ignore-keys
           (destructuring-bind (win x y state code time) args
             (let ((w (funcall window-of win)))
               (when w
                 (if (eq kind :button-press)
                     (interactors::do-button-press w x y state code time :button-press)
                     (interactors::do-button-release w x y state code time :button-release)))))))
        (:motion-notify
         (unless ignore-keys
           (destructuring-bind (win x y time) args
             (declare (ignore time))
             (let ((w (funcall window-of win)))
               (when w (interactors::do-motion-notify w x y *wl-display*))))))
        (:enter-notify
         (unless ignore-keys
           (destructuring-bind (win x y time) args
             (let ((w (funcall window-of win)))
               (when w (interactors::do-enter-notify w x y time))))))
        (:leave-notify
         (unless ignore-keys
           (destructuring-bind (win x y time) args
             (let ((w (funcall window-of win)))
               (when w (interactors::do-leave-notify w x y time))))))
        (:expose
         (destructuring-bind (win x y w h) args
           (let ((ow (funcall window-of win)))
             (when ow (interactors::do-exposure ow x y w h 0 *wl-display*)))))
        (:configure-notify
         (destructuring-bind (win x y w h) args
           (let ((ow (funcall window-of win)))
             (when ow (interactors::do-configure-notify ow x y w h nil)))))
        (:map-notify
         (interactors::do-map-notify (funcall window-of (first args))))
        (:unmap-notify
         (interactors::do-unmap-notify (funcall window-of (first args))))
        (:client-message
         (destructuring-bind (win type data format) args
           (interactors::do-client-message win type data format *wl-display*)))
        )
      t)))

(defvar *wl-redraw-all* nil
  "Set when every window must be drawn again: after a change of scale.  Not
an event, which DISCARD-PENDING-EVENTS could throw away.")

(defun wl-run-redraw-all ()
  "If the scale changed, have Opal draw every window again, at the new one."
  (when *wl-redraw-all*
    (setf *wl-redraw-all* nil)
    (dolist (w (remove-duplicates
                (loop for d being the hash-keys of *wl-drawable-to-window-table*
                        using (hash-value w)
                      when (and (wl-window-p d) (schema-p w)) collect w)))
      (opal:update w t))))

(defun wl-set-scale (scale)
  "The compositor prefers SCALE for Garnet's windows: draw them, and their
double buffers, at it from now on."
  (unless (= scale *wl-scale*)
    (setf *wl-scale* scale)
    (maphash (lambda (d w)
               (declare (ignore w))
               (when (and (wl-window-p d) (not (eq (wl-window-kind d) :root)))
                 (wl-rescale-surface (wl-window-pixels d) scale (wl-window-background d))
                 (wl-damage-all d)))
             *wl-drawable-to-window-table*)
    (maphash (lambda (buffer v)
               (declare (ignore v))
               (wl-rescale-surface buffer scale #xFFFFFF))
             *wl-window-buffers*)
    (clrhash *wl-layout-cache*)
    (setf *wl-redraw-all* t)))

(defun wl-event-handler (root-window ignore-keys)
  "Take one event for Garnet, waiting for it unless IGNORE-KEYS, and
dispatch it to the interactors."
  (declare (ignore root-window))
  (unless *wl-display*
    (return-from wl-event-handler nil))
  (setf *wl-thread* (bt:current-thread))
  (loop
    (wl-run-redraw-all)
    (wl-present-all)
    (wl-read-events)
    (wl-run-repeat)
    (let ((event (wl-pop-event)))
      (when event
        (return (wl-dispatch-event event ignore-keys))))
    (when ignore-keys
      (return nil))
    ;; Block until there is something, as the X backends do.  The main
    ;; loop is left through *EXIT-MAIN-EVENT-LOOP-FUNCTION*, which Opal
    ;; calls while handling the unmap or destroy.
    (when (and opal::*inside-main-event-loop*
               (not (opal::any-top-level-window-visible)))
      (return nil))
    (wl-wait nil)))


;;; Method Attachment Table

(defun attach-wl-methods (wl-device)
  (macrolet ((attach-wl-devices (&body keys)
               ;; Each KEY attaches the function WL-<KEY>.
               `(progn
                  ,@(loop for key in keys
                          for fn = (intern (format nil "WL-~A" (symbol-name key)) '#:gem)
                          collect `(attach-method wl-device ,key #',fn)))))
    (attach-wl-devices
      ;; Device & window queries
      :all-garnet-windows :beep :black-white-pixel :color-to-index
      :colormap-property :query-color :drawable-to-window :window-from-drawable
      :drawable-equal :check-wm-delete-window :window-debug-id :window-depth
      :window-has-grown :flush-output :device-batch-changes
      ;; Window lifecycle & management
      :create-window :delete-window :map-and-wait :reparent :raise-or-lower
      :initialize-window-borders :set-window-property :translate-coordinates
      :mouse-grab :set-drawable-to-window :set-draw-function-alist :set-draw-functions
      ;; Drawing
      :clear-area :draw-rectangle :draw-line :draw-lines :draw-points :draw-arc
      :draw-roundtangle :draw-text :draw-image :bit-blit :set-clip-mask
      ;; Fonts and text
      :font-exists-p :font-name-p :make-font-name :font-to-internal :delete-font
      :font-max-min-width :max-character-ascent :max-character-descent
      :character-width :text-width :text-extents
      ;; Pixmaps & images
      :create-pixmap :delete-pixmap :build-pixmap :copy-to-pixmap :create-image
      :create-image-array :image-size :image-bit :image-to-array :image-hot-spot
      :image-from-bits :device-image :window-to-image :read-an-image
      :write-an-image :stippled-p
      ;; Events & cut buffer
      :create-cursor :create-state-mask :get-cut-buffer :set-cut-buffer
      :discard-mouse-moved-events :discard-pending-events :event-handler
      :inject-event :translate-code
      ;; Interactors
      :check-double-press :set-interest-in-moved :translate-mouse-character
      :translate-character)
    (set-window-methods opal::window wl-device)))

;;; Register the device with GEM, make it the default, and initialize it.
(register-device :wl #'init-wl-device #'init-wl-device-post)
(setf *default-device-type* :wl)

;;; Opal and Lapidary test *X11-SERVER-AVAILABLE* to mean "there is a
;;; display to draw on".
(let ((wayland (uiop:getenv "WAYLAND_DISPLAY")))
  (setf *x11-server-available* wayland)
  (if wayland
      (progn
        (init-wl-device)
        (init-wl-device-post))
      (warn "WAYLAND_DISPLAY is not set; skipping Wayland device initialization.")))
