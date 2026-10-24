;;;; src/garnet/bridge.lisp — Antron Display Bridge for Garnet Wayland GEM
;;;; Replaces Garnet GEM drawing loops with Antron AVX-512 SIMD rasterizer
;;;; Copyright (C) 2026 Arthur Miller <arthur.miller@live.com>
;;;; SPDX-License-Identifier: MIT

(in-package :gem)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (export '(install-antron-gem
            uninstall-antron-gem
            with-antron-gem
            surface-cpu-context
            garnet-color-to-rgba
            antron-wl-clear-area
            antron-wl-draw-rectangle
            antron-wl-draw-roundtangle
            antron-wl-draw-line
            antron-wl-draw-text)
          :gem))

(declaim (optimize (speed 3) (safety 1)))

;;; ============================================================================
;;; Zero-Allocation Context Wrapping & Cache
;;; ============================================================================

(defvar *surface-context-cache* (make-hash-table :test #'eq)
  "Mapping from Garnet PX-SURFACE to wrapped Antron CPU-CONTEXT.")

(defun surface-cpu-context (s)
  "Wrap a Garnet PX-SURFACE S into an Antron CPU-CONTEXT with zero heap allocations in steady state."
  (declare (type gem::px-surface s))
  (let ((ctx (gethash s *surface-context-cache*))
        (pixels (gem::px-surface-pixels s)))
    (if (and ctx
             (eq (antron:cpu-context-pixels ctx) pixels)
             (= (antron:cpu-context-width ctx) (gem::px-surface-width s))
             (= (antron:cpu-context-height ctx) (gem::px-surface-height s)))
        ctx
        (let* ((w (gem::px-surface-width s))
               (h (gem::px-surface-height s))
               (new-ctx (antron:make-cpu-context w h :pixels pixels :stride w :format :argb)))
          (setf (gethash s *surface-context-cache*) new-ctx)
          new-ctx))))

;;; ============================================================================
;;; Color & Style Converters
;;; ============================================================================

(declaim (inline garnet-color-to-rgba))
(defun garnet-color-to-rgba (color &optional (default-alpha 1.0f0))
  "Extract (VALUES R G B A) as single-floats [0.0, 1.0] from Opal color schema or integer pixel."
  (cond
    ((and color (kr:schema-p color))
      (let ((r (float (or (kr:g-value color :red) 0.0) 1.0f0))
            (g (float (or (kr:g-value color :green) 0.0) 1.0f0))
            (b (float (or (kr:g-value color :blue) 0.0) 1.0f0)))
        (values r g b default-alpha)))
    ((integerp color)
      (let ((r (/ (ldb (byte 8 16) color) 255.0f0))
            (g (/ (ldb (byte 8 8) color) 255.0f0))
            (b (/ (ldb (byte 8 0) color) 255.0f0)))
        (values r g b default-alpha)))
    (t (values 0.0f0 0.0f0 0.0f0 default-alpha))))

;;; ============================================================================
;;; Antron-Accelerated GEM Drawing Methods
;;; ============================================================================

(defun antron-wl-clear-area (window &optional (x 0) (y 0) width height clear-buffer-p)
  "Clear WINDOW or its double-buffer to background using Antron AVX-512 SIMD memory clearing."
  (if clear-buffer-p
      (let ((buffer (kr:g-value window :buffer))
            (buffer-gc (kr:g-value window :buffer-gcontext)))
        (when (and (gem::px-surface-p buffer) buffer-gc)
          (let* ((bg-pixel (gem::px-gc-background buffer-gc))
                 (pixels (gem::px-surface-pixels buffer))
                 (sw (gem::px-surface-width buffer))
                 (sh (gem::px-surface-height buffer)))
            (if x
                (multiple-value-bind (dx dy dw dh)
                    (gem::dev-rect x y width height (gem::px-surface-scale buffer))
                  (let ((x0 (max 0 dx)) (x1 (min sw (+ dx dw)))
                        (y0 (max 0 dy)) (y1 (min sh (+ dy dh))))
                    (when (and (< x0 x1) (< y0 y1))
                      (let ((span-w (- x1 x0)))
                        (loop for row from y0 below y1 do
                          (antron::fill-span-opaque pixels (+ (* row sw) x0) span-w bg-pixel))))))
                (antron::clear-buffer-fast pixels (length pixels) bg-pixel)))))
      (let ((drawable (kr:g-value window :drawable)))
        (when (gem::wl-window-p drawable)
          (let* ((x (or x 0)) (y (or y 0))
                 (w (or width (gem::wl-window-width drawable)))
                 (h (or height (gem::wl-window-height drawable)))
                 (pixels-surface (gem::wl-window-pixels drawable))
                 (pixels (gem::px-surface-pixels pixels-surface))
                 (sw (gem::px-surface-width pixels-surface))
                 (sh (gem::px-surface-height pixels-surface))
                 (bg-pixel (gem::wl-window-background drawable)))
            (multiple-value-bind (dx dy dw dh)
                (gem::dev-rect x y w h (gem::wl-scale-of drawable))
              (let ((x0 (max 0 dx)) (x1 (min sw (+ dx dw)))
                    (y0 (max 0 dy)) (y1 (min sh (+ dy dh))))
                (if (and (= x0 0) (= y0 0) (= x1 sw) (= y1 sh))
                    (antron::clear-buffer-fast pixels (length pixels) bg-pixel)
                    (when (and (< x0 x1) (< y0 y1))
                      (let ((span-w (- x1 x0)))
                        (loop for row from y0 below y1 do
                          (antron::fill-span-opaque pixels (+ (* row sw) x0) span-w bg-pixel)))))))
            (gem::wl-damage drawable x y w h))))))

(defun antron-wl-draw-rectangle (window left top width height function line-style fill-style)
  "Draw rectangle on WINDOW using Antron AVX-512 SIMD rasterizer."
  (declare (ignore function))
  (let* ((drawable (gem::the-drawable window))
         (s (gem::wl-target drawable))
         (k (gem::px-surface-scale s))
         (thickness (if line-style (max 1 (or (kr:g-value line-style :line-thickness) 0)) 0))
         (ctx (surface-cpu-context s)))
    (when fill-style
      (multiple-value-bind (dx dy dw dh)
          (gem::dev-rect (+ left thickness) (+ top thickness)
                         (max 0 (- width (* 2 thickness))) (max 0 (- height (* 2 thickness))) k)
        (multiple-value-bind (r g b a)
            (garnet-color-to-rgba (kr:g-value fill-style :foreground-color))
          (antron:rasterize-rect ctx
                                 (float dx 1.0f0) (float dy 1.0f0)
                                 (float (+ dx dw) 1.0f0) (float (+ dy dh) 1.0f0)
                                 nil r g b a nil 0.0f0))))
    (when line-style
      (let* ((half (truncate thickness 2))
             (x0 (gem::dev-vertex (+ left half) k))
             (y0 (gem::dev-vertex (+ top half) k))
             (x1 (gem::dev-vertex (+ left half (max 0 (- width thickness))) k))
             (y1 (gem::dev-vertex (+ top half (max 0 (- height thickness))) k)))
        (multiple-value-bind (r g b a)
            (garnet-color-to-rgba (kr:g-value line-style :foreground-color))
          (antron:rasterize-rect ctx
                                 (float x0 1.0f0) (float y0 1.0f0)
                                 (float (max x0 x1) 1.0f0) (float (max y0 y1) 1.0f0)
                                 nil r g b a t (float (max 1 (* thickness k)) 1.0f0)))))
    (gem::wl-note-drawn drawable (1- left) (1- top) (+ width 2) (+ height 2))))

(defun antron-wl-draw-roundtangle (window left top width height corner-width corner-height function line-style fill-style)
  "Draw rounded rectangle on WINDOW using Antron analytic scanline SDF rasterizer."
  (declare (ignore function))
  (let* ((drawable (gem::the-drawable window))
         (s (gem::wl-target drawable))
         (k (gem::px-surface-scale s))
         (th (if line-style (max 1 (or (kr:g-value line-style :line-thickness) 0)) 0))
         (ctx (surface-cpu-context s))
         (dev-x (* left k))
         (dev-y (* top k))
         (dev-w (* width k))
         (dev-h (* height k))
         (dev-rx (* corner-width k))
         (dev-ry (* corner-height k)))
    (when fill-style
      (multiple-value-bind (r g b a)
          (garnet-color-to-rgba (kr:g-value fill-style :foreground-color))
        (antron:rasterize-round-rect ctx
                                    (float (+ dev-x (* th k)) 1.0f0)
                                    (float (+ dev-y (* th k)) 1.0f0)
                                    (float (- (+ dev-x dev-w) (* th k)) 1.0f0)
                                    (float (- (+ dev-y dev-h) (* th k)) 1.0f0)
                                    (float (max 0.0f0 (- dev-rx (* th k))) 1.0f0)
                                    (float (max 0.0f0 (- dev-ry (* th k))) 1.0f0)
                                    nil r g b a nil 0.0f0)))
    (when line-style
      (multiple-value-bind (r g b a)
          (garnet-color-to-rgba (kr:g-value line-style :foreground-color))
        (antron:rasterize-round-rect ctx
                                    (float dev-x 1.0f0)
                                    (float dev-y 1.0f0)
                                    (float (+ dev-x dev-w) 1.0f0)
                                    (float (+ dev-y dev-h) 1.0f0)
                                    (float dev-rx 1.0f0)
                                    (float dev-ry 1.0f0)
                                    nil r g b a t (float (max 1 (* th k)) 1.0f0))))
    (gem::wl-note-drawn drawable (1- left) (1- top) (+ width 2) (+ height 2))))

(defun antron-wl-draw-line (window x1 y1 x2 y2 function line-style &optional drawable)
  "Draw line on WINDOW using Antron AVX-512 SIMD rasterizer."
  (declare (ignore function))
  (let* ((drawable (or drawable (gem::the-drawable window)))
         (s (gem::wl-target drawable))
         (k (gem::px-surface-scale s)))
    (when line-style
      (let* ((ctx (surface-cpu-context s))
             (th (max 1 (or (kr:g-value line-style :line-thickness) 0)))
             (sw (float (max 1 (* th k)) 1.0f0))
             (dx0 (float (gem::dev-vertex x1 k) 1.0f0))
             (dy0 (float (gem::dev-vertex y1 k) 1.0f0))
             (dx1 (float (gem::dev-vertex x2 k) 1.0f0))
             (dy1 (float (gem::dev-vertex y2 k) 1.0f0)))
        (multiple-value-bind (r g b a)
            (garnet-color-to-rgba (kr:g-value line-style :foreground-color))
          (antron:rasterize-line ctx dx0 dy0 dx1 dy1 nil r g b a sw))
        (gem::wl-points-bbox-damage drawable (list (cons x1 y1) (cons x2 y2)) th)))))

(defun antron-wl-draw-text (window x y string font function line-style
                            &optional fill-background invert-p)
  "Draw text on WINDOW using Antron AVX-512 glyph alpha mask blitting."
  (declare (ignore function))
  (let* ((drawable (gem::the-drawable window))
         (s (gem::wl-target drawable))
         (str (string string))
         (tt-font (gem::wl-resolve-font window font)))
    (when (and drawable tt-font (plusp (length str)))
      (let* ((style-fg (if (and line-style (kr:schema-p line-style))
                           (gem::wl-color-to-pixel (kr:g-value line-style :foreground-color) 0)
                           0))
             (style-bg (if (and line-style (kr:schema-p line-style))
                           (gem::wl-color-to-pixel (kr:g-value line-style :background-color) #xFFFFFF)
                           #xFFFFFF))
             (fg (if invert-p style-bg style-fg))
             (k (gem::px-surface-scale s))
             (dpi (* gem::*wl-dpi* k))
             (ascent (truetype:font-ascent gem::*wl-dpi* tt-font))
             (descent (abs (truetype:font-descent gem::*wl-dpi* tt-font)))
             (width (truetype:text-line-width gem::*wl-dpi* tt-font str))
             (dx (gem::dev-edge x k)) (dy (gem::dev-edge y k))
             (cw (gem::px-surface-width s))
             (ch (gem::px-surface-height s))
             (stride (gem::px-surface-width s))
             (pixels (gem::px-surface-pixels s))
             (fg-r (ldb (byte 8 16) fg))
             (fg-g (ldb (byte 8 8) fg))
             (fg-b (ldb (byte 8 0) fg)))
        (when fill-background
          (multiple-value-bind (bx by bw bh)
              (gem::dev-rect x (- y ascent) (max 1 width) (max 1 (+ ascent descent)) k)
            (let ((bg-pix (if invert-p style-fg style-bg)))
              (loop for row from (max 0 by) below (min (+ by bh) ch) do
                (antron::fill-span-opaque pixels (+ (* row stride) (max 0 bx))
                                          (max 0 (min bw (- cw bx))) bg-pix)))))
        ;; Blit TrueType glyph masks directly using Antron's AVX-512 SIMD blend-glyph-mask
        (loop for (pen . image) across (gem::wl-layout tt-font str dpi)
              when (plusp (truetype:glyph-image-width image)) do
                (let ((gx (- (+ dx pen) (truetype:glyph-image-x image)))
                      (gy (- dy (truetype:glyph-image-y image))))
                  (antron:blend-glyph-mask pixels stride cw ch gx gy
                                          (truetype:glyph-image-data image)
                                          (truetype:glyph-image-width image)
                                          (truetype:glyph-image-height image)
                                          (truetype:glyph-image-stride image)
                                          fg-r fg-g fg-b 255 :argb)))
        (gem::wl-note-drawn drawable (- x 2) (- y ascent 2) (+ width 4) (+ ascent descent 4))))))

;;; ============================================================================
;;; Bridge Lifecycle & GEM Device Attachment
;;; ============================================================================

(defvar *saved-wl-methods* (make-hash-table :test #'eq)
  "Saved original GEM method pointers for restoring stock Garnet routines.")

(defun install-antron-gem (&optional (device gem::wl-device))
  "Install Antron AVX-512 accelerated drawing methods onto Garnet's WL-DEVICE."
  (let ((methods '((:clear-area . antron-wl-clear-area)
                   (:draw-rectangle . antron-wl-draw-rectangle)
                   (:draw-roundtangle . antron-wl-draw-roundtangle)
                   (:draw-line . antron-wl-draw-line)
                   (:draw-text . antron-wl-draw-text))))
    (dolist (m methods)
      (let* ((key (car m))
             (fn (cdr m))
             (num (gem::find-or-create-name key))
             (cur-methods (kr:g-value device :methods)))
        (when (and cur-methods (< num (length cur-methods)))
          (setf (gethash key *saved-wl-methods*) (aref cur-methods num)))
        (gem::attach-method device key (symbol-function fn))))
    (gem::set-window-methods opal::window device)
    t))

(defun uninstall-antron-gem (&optional (device gem::wl-device))
  "Restore default Garnet WL drawing methods."
  (maphash (lambda (key old-fn)
             (when old-fn
               (gem::attach-method device key old-fn)))
           *saved-wl-methods*)
  (gem::set-window-methods opal::window device)
  t)

(defmacro with-antron-gem (&body body)
  "Execute BODY with Antron GEM acceleration enabled, restoring original methods on exit."
  `(progn
     (install-antron-gem)
     (unwind-protect
          (progn ,@body)
       (uninstall-antron-gem))))
