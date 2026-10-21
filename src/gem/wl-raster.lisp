;;; -*- Mode: LISP; Syntax: Common-Lisp; Package: GEM; Base: 10 -*-
;;;
;;; A software rasterizer with X11 semantics, for the Wayland backend.
;;;
;;; Wayland has no drawing requests: a client renders every pixel itself
;;; and hands the compositor finished buffers.  Opal was written against
;;; X11, so this file draws the way an X server does, as far as Opal can
;;; tell: the sixteen raster functions (Opal's feedback objects draw with
;;; :XOR), solid, stippled and opaque-stippled fills, clip rectangles,
;;; thin (Bresenham) and wide lines with X's caps and joins, dashes, arcs
;;; and pie slices, polygons by the even-odd or winding rule, bitmaps
;;; drawn in foreground and background, and CopyArea.
;;;
;;; A drawable is a PX-SURFACE: a vector of 32-bit pixels #x00RRGGBB, as
;;; the X backends use, or of 0s and 1s for a depth-1 pixmap.  Everything
;;; is reduced to horizontal spans, which PX-SPAN clips and paints.
;;;

(in-package :gem)

(defstruct (px-surface (:constructor %make-px-surface))
  (width 0 :type fixnum)
  (height 0 :type fixnum)
  (depth 24 :type fixnum)
  (pixels (make-array 0 :element-type '(unsigned-byte 32))
   :type (simple-array (unsigned-byte 32) (*))))

(defun make-px-surface (width height &key (depth 24) (initial 0))
  (let ((w (max 1 width)) (h (max 1 height)))
    (%make-px-surface :width w :height h :depth depth
                      :pixels (make-array (* w h) :element-type '(unsigned-byte 32)
                                                  :initial-element initial))))

(defun px-resize-surface (s width height background)
  "Give S a new size, keeping its pixels where they were and filling what
is new with BACKGROUND."
  (let ((w (max 1 width)) (h (max 1 height)))
    (unless (and (= w (px-surface-width s)) (= h (px-surface-height s)))
      (let ((new (make-array (* w h) :element-type '(unsigned-byte 32)
                                     :initial-element background))
            (old (px-surface-pixels s))
            (ow (px-surface-width s))
            (cw (min w (px-surface-width s))))
        (dotimes (y (min h (px-surface-height s)))
          (replace new old :start1 (* y w) :start2 (* y ow) :end2 (+ (* y ow) cw)))
        (setf (px-surface-width s) w
              (px-surface-height s) h
              (px-surface-pixels s) new)))
    s))

;;; The graphics context: what an X GC holds that Opal sets.

(defstruct px-gc
  (function 3 :type fixnum)             ; GXcopy
  (foreground 0 :type (unsigned-byte 32))
  (background #xFFFFFF :type (unsigned-byte 32))
  (line-width 0 :type fixnum)
  (line-style :solid)                   ; :solid :dash :double-dash
  (cap-style :butt)                     ; :not-last :butt :round :projecting
  (join-style :miter)                   ; :miter :round :bevel
  (dashes '(4 4))
  (fill-style :solid)                   ; :solid :tiled :stippled :opaque-stippled
  (fill-rule :even-odd)                 ; :even-odd :winding
  (stipple nil)                         ; a PX-SURFACE or NIL
  (clip :none)                          ; :NONE or a list of (X Y W H)
  (opal-style nil))                     ; the Opal style last set, for caching

(defconstant +px-gx-copy+ 3)
(defconstant +px-gx-noop+ 5)
(defconstant +px-gx-xor+ 6)

(declaim (inline px-op))
(defun px-op (fn src dst mask)
  (declare (type fixnum fn) (type (unsigned-byte 32) src dst mask))
  (logand mask
          (case fn
            (0 0)                                ; clear
            (1 (logand src dst))                 ; and
            (2 (logand src (lognot dst)))        ; and-reverse
            (3 src)                              ; copy
            (4 (logand (lognot src) dst))        ; and-inverted
            (5 dst)                              ; no-op
            (6 (logxor src dst))                 ; xor
            (7 (logior src dst))                 ; or
            (8 (lognot (logior src dst)))        ; nor
            (9 (lognot (logxor src dst)))        ; equiv
            (10 (lognot dst))                    ; invert
            (11 (logior src (lognot dst)))       ; or-reverse
            (12 (lognot src))                    ; copy-inverted
            (13 (logior (lognot src) dst))       ; or-inverted
            (14 (lognot (logand src dst)))       ; nand
            (t #xFFFFFFFF))))                    ; set

(declaim (inline px-mask))
(defun px-mask (s)
  (if (= (px-surface-depth s) 1) 1 #xFFFFFF))

;;; Spans

(defun px-row-intervals (s clip y)
  "The intervals [A B) of row Y that CLIP lets through, within S, sorted
and disjoint, as a list of conses."
  (declare (type fixnum y))
  (let ((w (px-surface-width s)))
    (if (eq clip :none)
        (list (cons 0 w))
        (let ((ivs '()))
          (dolist (r clip)
            (destructuring-bind (rx ry rw rh) r
              (when (and (<= ry y) (< y (+ ry rh)))
                (let ((a (max 0 rx)) (b (min w (+ rx rw))))
                  (when (< a b) (push (cons a b) ivs))))))
          (if (cdr ivs)
              ;; Merge overlapping rectangles, so no pixel is painted twice:
              ;; that would undo an :XOR.
              (let ((sorted (sort ivs #'< :key #'car)) (out '()))
                (dolist (iv sorted (nreverse out))
                  (if (and out (<= (car iv) (cdar out)))
                      (setf (cdar out) (max (cdar out) (cdr iv)))
                      (push (cons (car iv) (cdr iv)) out))))
              ivs)))))

(defun px-paint (s gc y a b)
  "Paint pixels [A B) of row Y of S with GC, unclipped."
  (declare (type px-surface s) (type px-gc gc) (type fixnum y a b)
           (optimize (speed 3) (safety 0)))
  (let* ((pixels (px-surface-pixels s))
         (row (* y (px-surface-width s)))
         (fn (px-gc-function gc))
         (mask (px-mask s))
         (fg (logand mask (px-gc-foreground gc)))
         (bg (logand mask (px-gc-background gc)))
         (fill (px-gc-fill-style gc))
         (st (px-gc-stipple gc)))
    (declare (type (simple-array (unsigned-byte 32) (*)) pixels)
             (type fixnum row fn) (type (unsigned-byte 32) mask fg bg))
    (cond
      ((or (eq fill :solid) (null st))
       (if (= fn +px-gx-copy+)
           (fill pixels fg :start (+ row a) :end (+ row b))
           (loop for i of-type fixnum from (+ row a) below (+ row b)
                 do (setf (aref pixels i) (px-op fn fg (aref pixels i) mask)))))
      (t
       (let* ((st-pixels (px-surface-pixels st))
              (sw (px-surface-width st))
              (st-row (* sw (mod y (px-surface-height st))))
              (tiled (eq fill :tiled))
              (opaque (eq fill :opaque-stippled)))
         (declare (type (simple-array (unsigned-byte 32) (*)) st-pixels)
                  (type fixnum sw st-row))
         (loop for x of-type fixnum from a below b
               for i of-type fixnum from (+ row a)
               for bit = (aref st-pixels (+ st-row (mod x sw)))
               do (cond (tiled
                         (setf (aref pixels i) (px-op fn bit (aref pixels i) mask)))
                        ((/= bit 0)
                         (setf (aref pixels i) (px-op fn fg (aref pixels i) mask)))
                        (opaque
                         (setf (aref pixels i) (px-op fn bg (aref pixels i) mask))))))))))

(defun px-span (s gc y x0 x1)
  "Paint pixels [X0 X1) of row Y of S with GC, within its clip."
  (declare (type fixnum y x0 x1))
  (when (and (< x0 x1) (<= 0 y) (< y (px-surface-height s))
             (/= (px-gc-function gc) +px-gx-noop+))
    (let ((clip (px-gc-clip gc)))
      (if (and (consp clip) (null (cdr clip)))
          ;; The usual case, one rectangle: no consing.
          (destructuring-bind (rx ry rw rh) (car clip)
            (when (and (<= ry y) (< y (+ ry rh)))
              (let ((a (max x0 rx 0))
                    (b (min x1 (+ rx rw) (px-surface-width s))))
                (when (< a b) (px-paint s gc y a b)))))
          (if (eq clip :none)
              (let ((a (max x0 0)) (b (min x1 (px-surface-width s))))
                (when (< a b) (px-paint s gc y a b)))
              (dolist (iv (px-row-intervals s clip y))
                (let ((a (max x0 (car iv))) (b (min x1 (cdr iv))))
                  (when (< a b) (px-paint s gc y a b)))))))))

(defun px-point (s gc x y)
  (px-span s gc y x (1+ x)))

(defun px-fill-rectangle (s gc x y w h)
  (loop for row from (max y 0) below (min (+ y h) (px-surface-height s))
        do (px-span s gc row x (+ x w))))

(defun px-clear-rectangle (s x y w h pixel)
  "Fill a rectangle of S with PIXEL, ignoring any GC."
  (let* ((sw (px-surface-width s))
         (x0 (max 0 x)) (x1 (min sw (+ x w)))
         (pixels (px-surface-pixels s)))
    (when (< x0 x1)
      (loop for row from (max y 0) below (min (+ y h) (px-surface-height s))
            do (fill pixels pixel :start (+ (* row sw) x0) :end (+ (* row sw) x1))))))

;;; Polygons

(defun px-fill-paths (s gc paths rule)
  "Fill PATHS, a list of closed polygons, each a vector of coordinates
X0 Y0 X1 Y1 ..., together, by RULE (:EVEN-ODD or :WINDING).  As in X, a
pixel's centre is at its integer coordinates, and the pixel is drawn when
its centre is inside, or on a left or top edge."
  (let ((edges '()) (ymin most-positive-fixnum) (ymax most-negative-fixnum))
    (dolist (p paths)
      (let ((n (floor (length p) 2)))
        (when (>= n 3)
          (dotimes (i n)
            (let* ((j (mod (1+ i) n))
                   (x0 (float (aref p (* 2 i)) 1d0)) (y0 (float (aref p (1+ (* 2 i))) 1d0))
                   (x1 (float (aref p (* 2 j)) 1d0)) (y1 (float (aref p (1+ (* 2 j))) 1d0)))
              (unless (= y0 y1)
                (setf ymin (min ymin (floor (min y0 y1)))
                      ymax (max ymax (ceiling (max y0 y1))))
                (push (if (< y0 y1)
                          (vector x0 y0 x1 y1 1)
                          (vector x1 y1 x0 y0 -1))
                      edges)))))))
    (when edges
      (let ((edges (sort (coerce edges 'simple-vector) #'< :key (lambda (e) (aref e 1))))
            (xs (make-array 16 :adjustable t :fill-pointer 0)))
        (loop for y from (max ymin 0) to (min ymax (1- (px-surface-height s)))
              for yc = (float y 1d0)
              do (setf (fill-pointer xs) 0)
                 (loop for e across edges
                       while (<= (aref e 1) yc)
                       do (let ((ey0 (aref e 1)) (ey1 (aref e 3)))
                            (when (and (<= ey0 yc) (< yc ey1))
                              (let ((ex0 (aref e 0)) (ex1 (aref e 2)))
                                (vector-push-extend
                                 (cons (+ ex0 (/ (* (- yc ey0) (- ex1 ex0)) (- ey1 ey0)))
                                       (aref e 4))
                                 xs)))))
                 (when (plusp (fill-pointer xs))
                   (let ((sorted (sort xs #'< :key #'car)))
                     (flet ((span (xa xb)
                              (px-span s gc y (ceiling xa) (ceiling xb))))
                       (if (eq rule :winding)
                           (let ((wind 0) (start 0d0))
                             (loop for (x . dir) across sorted
                                   do (let ((was wind))
                                        (incf wind dir)
                                        (cond ((and (zerop was) (/= wind 0)) (setf start x))
                                              ((and (/= was 0) (zerop wind)) (span start x))))))
                           (loop for i from 0 below (1- (length sorted)) by 2
                                 do (span (car (aref sorted i)) (car (aref sorted (1+ i))))))))))))))

(defun px-fill-polygon (s gc coords &optional (rule (px-gc-fill-rule gc)))
  (px-fill-paths s gc (list (coerce coords 'simple-vector)) rule))

;;; Thin lines

(defun px-dash-on-p (gc dash-pos)
  "Whether DASH-POS pixels along a dashed line falls in an \"on\" dash."
  (let* ((dashes (or (px-gc-dashes gc) '(4 4)))
         (period (reduce #'+ dashes))
         (pos (mod dash-pos (max 1 period))))
    (loop for d in dashes
          for on = t then (not on)
          do (if (< pos d) (return on) (decf pos d))
          finally (return t))))

(defun px-thin-line (s gc x0 y0 x1 y1 &key skip-first skip-last (dash-start 0))
  "Draw a zero-width line from (X0,Y0) to (X1,Y1), both ends included unless
SKIP-FIRST or SKIP-LAST.  Returns the dash position at its end."
  (let* ((dx (abs (- x1 x0))) (dy (abs (- y1 y0)))
         (sx (if (< x0 x1) 1 -1)) (sy (if (< y0 y1) 1 -1))
         (style (px-gc-line-style gc))
         (dashed (member style '(:dash :on-off-dash :double-dash)))
         (steps (max dx dy))
         (x x0) (y y0) (err (- dx dy)) (pos dash-start))
    (if (and (not dashed) (= dy 0))
        ;; A horizontal line is one span.
        (let ((a (if skip-first (+ x0 sx) x0))
              (b (if skip-last (- x1 sx) x1)))
          (when (if (= sx 1) (<= a b) (>= a b))
            (px-span s gc y0 (min a b) (1+ (max a b))))
          (+ dash-start steps))
        (progn
          (dotimes (i (1+ steps))
            (unless (or (and skip-first (= i 0)) (and skip-last (= i steps)))
              (if (or (not dashed) (px-dash-on-p gc pos))
                  (px-point s gc x y)
                  (when (eq style :double-dash)
                    (let ((fg (px-gc-foreground gc)))
                      (setf (px-gc-foreground gc) (px-gc-background gc))
                      (unwind-protect (px-point s gc x y)
                        (setf (px-gc-foreground gc) fg))))))
            (incf pos)
            (let ((e2 (* 2 err)))
              (when (> e2 (- dy)) (decf err dy) (incf x sx))
              (when (< e2 dx) (incf err dx) (incf y sy))))
          pos))))

;;; Wide lines, built as polygons and filled together, so no pixel is
;;; painted twice where pieces overlap.

(defun px-circle-path (cx cy r)
  (let* ((n (max 8 (ceiling (* 2 pi r) 2)))
         (v (make-array (* 2 n))))
    (dotimes (i n v)
      (let ((a (/ (* 2 pi i) n)))
        (setf (aref v (* 2 i)) (+ cx (* r (cos a)))
              (aref v (1+ (* 2 i))) (+ cy (* r (sin a))))))))

(defun px-orient (path)
  "PATH, reversed if need be so that it winds clockwise on screen, so that
pieces filled together by the winding rule add up rather than cancel."
  (let ((n (floor (length path) 2)) (area 0))
    (dotimes (i n)
      (let ((j (mod (1+ i) n)))
        (incf area (- (* (aref path (* 2 i)) (aref path (1+ (* 2 j))))
                      (* (aref path (* 2 j)) (aref path (1+ (* 2 i))))))))
    (if (minusp area)
        (let ((r (make-array (length path))))
          (dotimes (i n r)
            (setf (aref r (* 2 i)) (aref path (* 2 (- n i 1)))
                  (aref r (1+ (* 2 i))) (aref path (1+ (* 2 (- n i 1)))))))
        path)))

(defun px-stroke-paths (points width cap join closed)
  "Polygons covering a polyline through POINTS, a list of (X . Y), stroked
WIDTH wide, X11 style.  Closed when CLOSED: then the ends are joined, not
capped."
  (let* ((hw (/ width 2d0))
         (pts (coerce points 'simple-vector))
         (n (length pts))
         (paths '()))
    (flet ((px (i) (float (car (aref pts i)) 1d0))
           (py (i) (float (cdr (aref pts i)) 1d0))
           (add (&rest coords) (push (coerce coords 'simple-vector) paths)))
      (labels ((offset (i j)
                 ;; The offset of the line from point I to J, perpendicular,
                 ;; HW long.
                 (let* ((dx (- (px j) (px i))) (dy (- (py j) (py i)))
                        (len (sqrt (+ (* dx dx) (* dy dy)))))
                   (if (zerop len)
                       (values 0d0 0d0 0d0 0d0)
                       (values (* hw (/ (- dy) len)) (* hw (/ dx len))
                               (/ dx len) (/ dy len)))))
               (cap (i j at-start)
                 ;; The cap at point I of the segment I..J.
                 (multiple-value-bind (nx ny ux uy) (offset i j)
                   (let ((x (px i)) (y (py i)))
                     (case cap
                       (:round (push (px-circle-path x y hw) paths))
                       (:projecting
                        (let ((ex (* hw ux (if at-start -1 1)))
                              (ey (* hw uy (if at-start -1 1))))
                          (add (+ x nx) (+ y ny) (+ x nx ex) (+ y ny ey)
                               (- (+ x ex) nx) (- (+ y ey) ny) (- x nx) (- y ny))))))))
               (join (h i j)
                 ;; The join at point I between segments H..I and I..J.
                 (multiple-value-bind (n1x n1y) (offset h i)
                   (multiple-value-bind (n2x n2y) (offset i j)
                     (let ((x (px i)) (y (py i))
                           (dot (+ (* n1x n2x) (* n1y n2y))))
                       (case join
                         (:round (push (px-circle-path x y hw) paths))
                         (t
                          (add x y (+ x n1x) (+ y n1y) (+ x n2x) (+ y n2y))
                          (add x y (- x n1x) (- y n1y) (- x n2x) (- y n2y))
                          ;; X's miter limit: joins sharper than 11 degrees
                          ;; are beveled.
                          (when (and (eq join :miter)
                                     (> (+ (* hw hw) dot) (* hw hw 0.0184d0)))
                            (let* ((k (/ (* hw hw) (+ (* hw hw) dot)))
                                   (tx (* k (+ n1x n2x))) (ty (* k (+ n1y n2y))))
                              (add x y (+ x n1x) (+ y n1y) (+ x tx) (+ y ty) (+ x n2x) (+ y n2y))
                              (add x y (- x n1x) (- y n1y) (- x tx) (- y ty) (- x n2x) (- y n2y)))))))))))
        (cond
          ((= n 1)
           (let ((x (px 0)) (y (py 0)))
             (if (eq cap :round)
                 (push (px-circle-path x y hw) paths)
                 (add (- x hw) (- y hw) (+ x hw) (- y hw) (+ x hw) (+ y hw) (- x hw) (+ y hw)))))
          (t
           (dotimes (i (1- n))
             (multiple-value-bind (nx ny) (offset i (1+ i))
               (let ((x0 (px i)) (y0 (py i)) (x1 (px (1+ i))) (y1 (py (1+ i))))
                 (add (+ x0 nx) (+ y0 ny) (+ x1 nx) (+ y1 ny)
                      (- x1 nx) (- y1 ny) (- x0 nx) (- y0 ny)))))
           (loop for i from 1 below (1- n)
                 do (join (1- i) i (1+ i)))
           (if closed
               (when (> n 2) (join (- n 2) 0 1))
               (progn (cap 0 1 t)
                      (cap (1- n) (- n 2) nil)))))))
    (mapcar #'px-orient paths)))

(defun px-split-dashes (points gc)
  "Split the polyline through POINTS into its dashes: a list of polylines
that are on and, for :DOUBLE-DASH, a second list that are off."
  (let* ((dashes (or (px-gc-dashes gc) '(4 4)))
         (dv (coerce dashes 'simple-vector))
         (di 0) (left (float (aref dv 0) 1d0)) (on t)
         (current (list (car points)))
         (ons '()) (offs '()))
    (flet ((finish ()
             (when (cdr current)
               (if on (push (nreverse current) ons) (push (nreverse current) offs)))))
      (loop for (a b) on points
            while b
            do (let* ((ax (float (car a) 1d0)) (ay (float (cdr a) 1d0))
                      (bx (float (car b) 1d0)) (by (float (cdr b) 1d0))
                      (len (sqrt (+ (expt (- bx ax) 2) (expt (- by ay) 2))))
                      (done 0d0))
                 (loop while (> (- len done) left)
                       do (incf done left)
                          (let ((p (cons (+ ax (* (- bx ax) (/ done len)))
                                         (+ ay (* (- by ay) (/ done len))))))
                            (push p current)
                            (finish)
                            (setf current (list p)
                                  on (not on)
                                  di (mod (1+ di) (length dv))
                                  left (float (aref dv di) 1d0))))
                 (decf left (- len done))
                 (push b current)))
      (finish))
    (values (nreverse ons) (nreverse offs))))

(defun px-wide-polyline (s gc points closed)
  (let ((w (px-gc-line-width gc))
        (cap (px-gc-cap-style gc))
        (join (px-gc-join-style gc))
        (style (px-gc-line-style gc)))
    (when (eq cap :not-last) (setf cap :butt))
    (if (member style '(:dash :on-off-dash :double-dash))
        (multiple-value-bind (ons offs)
            (px-split-dashes (if closed (append points (list (car points))) points) gc)
          (px-fill-paths s gc (loop for p in ons append (px-stroke-paths p w cap join nil))
                         :winding)
          (when (and offs (eq style :double-dash))
            (let ((fg (px-gc-foreground gc)))
              (setf (px-gc-foreground gc) (px-gc-background gc))
              (unwind-protect
                   (px-fill-paths s gc (loop for p in offs
                                             append (px-stroke-paths p w cap join nil))
                                  :winding)
                (setf (px-gc-foreground gc) fg)))))
        (px-fill-paths s gc (px-stroke-paths points w cap join closed) :winding))))

;;; Requests, as X has them

(defun px-polyline (s gc points)
  "PolyLine through POINTS, a list of (X . Y) with integer coordinates."
  (when points
    (let ((closed (and (cddr points) (equal (car points) (car (last points))))))
      (if (zerop (px-gc-line-width gc))
          (let ((pos 0)
                (last-segment (- (length points) 2)))
            ;; Each joint and, when closed, the start drawn once, so that an
            ;; :XOR polyline leaves no holes.
            (if (null (cdr points))
                (px-point s gc (caar points) (cdar points))
                (loop for (a b) on points
                      for k from 0
                      while b
                      do (setf pos (px-thin-line s gc (car a) (cdr a) (car b) (cdr b)
                                                 :skip-first (> k 0)
                                                 :skip-last (and closed (= k last-segment))
                                                 :dash-start pos)))))
          (px-wide-polyline s gc (if closed (butlast points) points) closed)))))

(defun px-segment (s gc x1 y1 x2 y2)
  (if (zerop (px-gc-line-width gc))
      (px-thin-line s gc x1 y1 x2 y2 :skip-last (eq (px-gc-cap-style gc) :not-last))
      (px-wide-polyline s gc (list (cons x1 y1) (cons x2 y2)) nil)))

(defun px-rectangle-outline (s gc x y w h)
  "PolyRectangle: the outline of the rectangle from (X,Y) to (X+W,Y+H)."
  (let ((lw (px-gc-line-width gc)))
    (if (and (zerop lw) (member (px-gc-line-style gc) '(:solid nil)))
        (progn
          (px-span s gc y x (+ x w 1))
          (when (plusp h)
            (px-span s gc (+ y h) x (+ x w 1)))
          (loop for row from (1+ y) below (+ y h)
                do (px-point s gc x row)
                   (when (plusp w) (px-point s gc (+ x w) row))))
        (if (zerop lw)
            (px-polyline s gc (list (cons x y) (cons (+ x w) y) (cons (+ x w) (+ y h))
                                    (cons x (+ y h)) (cons x y)))
            (let ((hw (/ lw 2d0)))
              ;; A closed, mitered rectangle: the outer box less the inner.
              (px-fill-paths s gc
                             (list (vector (- x hw) (- y hw) (+ x w hw) (- y hw)
                                           (+ x w hw) (+ y h hw) (- x hw) (+ y h hw))
                                   (if (and (> w lw) (> h lw))
                                       (vector (+ x hw) (+ y hw) (- (+ x w) hw) (+ y hw)
                                               (- (+ x w) hw) (- (+ y h) hw) (+ x hw) (- (+ y h) hw))
                                       (vector)))
                             :even-odd))))))

(defun px-arc-points (x y w h angle1 angle2)
  "Points along the arc of the ellipse in the box (X Y W H), from ANGLE1
for ANGLE2 radians, counterclockwise from three o'clock, as X has arcs."
  (let* ((cx (+ x (/ w 2d0))) (cy (+ y (/ h 2d0)))
         (rx (/ w 2d0)) (ry (/ h 2d0))
         (sweep (max (- (* 2 pi)) (min (* 2 pi) angle2)))
         (n (max 4 (ceiling (* (abs sweep) (max rx ry 1)) 2))))
    (loop for i from 0 to n
          for a = (+ angle1 (* sweep (/ i n)))
          collect (cons (+ cx (* rx (cos a))) (- cy (* ry (sin a)))))))

(defun px-arc-outline (s gc x y w h angle1 angle2)
  (let ((pts (px-arc-points x y w h angle1 angle2))
        (full (>= (abs angle2) (* 2 pi 0.9999))))
    (if (zerop (px-gc-line-width gc))
        (px-polyline s gc (let ((ipts (mapcar (lambda (p) (cons (round (car p)) (round (cdr p)))) pts)))
                            ;; Drop repeated points, so joints are not skipped
                            ;; twice.
                            (loop for (a . rest) on ipts
                                  unless (and rest (equal a (car rest)))
                                    collect a)))
        (let ((old (px-gc-join-style gc)))
          (setf (px-gc-join-style gc) :round)
          (unwind-protect
               (px-wide-polyline s gc (if full (butlast pts) pts) full)
            (setf (px-gc-join-style gc) old))))))

(defun px-arc-fill (s gc x y w h angle1 angle2)
  "PolyFillArc in pie-slice mode."
  (let* ((pts (px-arc-points x y w h angle1 angle2))
         (full (>= (abs angle2) (* 2 pi 0.9999)))
         (cx (+ x (/ w 2d0))) (cy (+ y (/ h 2d0)))
         (coords (loop for (px . py) in (if full pts (cons (cons cx cy) pts))
                       collect px collect py)))
    (px-fill-polygon s gc coords :winding)))

;;; Images

(defun px-put-bitmap (s gc x y w h data bytes-per-line)
  "PutImage of a bitmap: DATA holds H rows of BYTES-PER-LINE bytes, bits
LSB first; 1s are drawn in the foreground, 0s in the background."
  (let ((fg (px-gc-foreground gc)) (fill (px-gc-fill-style gc)))
    (setf (px-gc-fill-style gc) :solid)
    (unwind-protect
         (dotimes (row h)
           (let ((start nil) (on nil))
             (flet ((flush (end)
                      (when start
                        (setf (px-gc-foreground gc) (if on fg (px-gc-background gc)))
                        (px-span s gc (+ y row) (+ x start) (+ x end)))))
               (dotimes (col w)
                 (let* ((i (+ (* row bytes-per-line) (floor col 8)))
                        (bit (and (< i (array-total-size data))
                                  (logbitp (mod col 8) (row-major-aref data i)))))
                   (unless (and start (eq bit on))
                     (flush col)
                     (setf start col on bit))))
               (flush w))))
      (setf (px-gc-foreground gc) fg
            (px-gc-fill-style gc) fill))))

(defun px-put-pixels (s gc x y pixels)
  "PutImage of PIXELS, a (HEIGHT WIDTH) array of pixel values."
  (destructuring-bind (h w) (array-dimensions pixels)
    (let ((fg (px-gc-foreground gc)) (fill (px-gc-fill-style gc)))
      (setf (px-gc-fill-style gc) :solid)
      (unwind-protect
           (dotimes (row h)
             (dotimes (col w)
               (setf (px-gc-foreground gc) (logand #xFFFFFFFF (or (aref pixels row col) 0)))
               (px-point s gc (+ x col) (+ y row))))
        (setf (px-gc-foreground gc) fg
              (px-gc-fill-style gc) fill)))))

(defun px-copy-area (src dst gc sx sy w h dx dy)
  "CopyArea from SRC to DST through GC's function and clip."
  (let* ((sw (px-surface-width src))
         ;; Clip the source rectangle to SRC.
         (x0 (max sx 0)) (y0 (max sy 0))
         (x1 (min (+ sx w) sw)) (y1 (min (+ sy h) (px-surface-height src)))
         (dx (+ dx (- x0 sx))) (dy (+ dy (- y0 sy)))
         (w (- x1 x0)) (h (- y1 y0)))
    (when (and (plusp w) (plusp h))
      (let* ((spix (px-surface-pixels src))
             ;; Copying within one surface: read from a copy, so overlapping
             ;; rectangles come out right.
             (copy (if (eq src dst)
                       (let ((c (make-array (* w h) :element-type '(unsigned-byte 32))))
                         (dotimes (r h c)
                           (replace c spix :start1 (* r w)
                                           :start2 (+ (* (+ y0 r) sw) x0)
                                           :end2 (+ (* (+ y0 r) sw) x0 w))))
                       nil))
             (fn (px-gc-function gc))
             (mask (px-mask dst))
             (dpix (px-surface-pixels dst))
             (dw (px-surface-width dst))
             (from-bitmap (and (= (px-surface-depth src) 1) (/= (px-surface-depth dst) 1))))
        (dotimes (r h)
          (let ((row (+ dy r)))
            (when (< -1 row (px-surface-height dst))
              (dolist (iv (px-row-intervals dst (px-gc-clip gc) row))
                (let ((a (max dx (car iv))) (b (min (+ dx w) (cdr iv))))
                  (loop for x from a below b
                        for v = (if copy
                                    (aref copy (+ (* r w) (- x dx)))
                                    (aref spix (+ (* (+ y0 r) sw) x0 (- x dx))))
                        for src-pixel = (if from-bitmap
                                            (if (zerop v) (px-gc-background gc) (px-gc-foreground gc))
                                            v)
                        for i = (+ (* row dw) x)
                        do (setf (aref dpix i) (px-op fn src-pixel (aref dpix i) mask))))))))))))

;;; Text

(defun px-blend-alpha (s clip x y w h data stride colour)
  "Blend COLOUR into S through the alpha map DATA, W by H with rows STRIDE
bytes apart, its top left at (X,Y), within CLIP."
  (declare (type fixnum x y w h stride) (type (unsigned-byte 32) colour)
           (type (simple-array (unsigned-byte 8) (*)) data))
  (let ((pixels (px-surface-pixels s))
        (sw (px-surface-width s))
        (fr (ldb (byte 8 16) colour))
        (fgc (ldb (byte 8 8) colour))
        (fb (ldb (byte 8 0) colour)))
    (declare (type (simple-array (unsigned-byte 32) (*)) pixels) (type fixnum sw fr fgc fb))
    (loop for row from (max 0 (- y)) below h
          for py = (+ y row)
          while (< py (px-surface-height s))
          do (dolist (iv (px-row-intervals s clip py))
               (loop for col from (max 0 (- (car iv) x)) below (min w (- (cdr iv) x))
                     for a = (aref data (+ (* row stride) col))
                     unless (zerop a)
                       do (let ((i (+ (* py sw) x col)))
                            (if (= a 255)
                                (setf (aref pixels i) colour)
                                (let* ((d (aref pixels i)) (na (- 255 a)))
                                  (setf (aref pixels i)
                                        (logior
                                         (ash (floor (+ (* a fr) (* na (ldb (byte 8 16) d))) 255) 16)
                                         (ash (floor (+ (* a fgc) (* na (ldb (byte 8 8) d))) 255) 8)
                                         (floor (+ (* a fb) (* na (ldb (byte 8 0) d))) 255)))))))))))
