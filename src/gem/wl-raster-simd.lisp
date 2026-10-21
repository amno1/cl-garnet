;;; -*- Mode: LISP; Syntax: Common-Lisp; Package: GEM; Base: 10 -*-
;;;
;;; AVX-512 versions of the rasterizer's row kernels (wl-raster.lisp), 16
;;; pixels at a time, for an SBCL whose sb-simd has AVX-512F.  Elsewhere
;;; this file compiles to nothing, and on a CPU without AVX-512F the
;;; kernels are not installed: either way the scalar kernels run.
;;;
;;; Each kernel works through system area pointers, with no bounds checks:
;;; the spans it is given are already clipped.  A span's last, partial
;;; group of 16 is read and written through a mask.  They give the same
;;; pixels as the scalar kernels, bit for bit.
;;;

(in-package :gem)

(eval-when (:compile-toplevel :load-toplevel :execute)
  #+sbcl (ignore-errors (require :sb-simd))
  ;; Stock SBCL's sb-simd has an AVX512F package too, without the masked
  ;; SAP accessors these kernels use: ask for every operation.
  (when (and (find-package "SB-SIMD-AVX512F")
             (every (lambda (name)
                      (let ((s (find-symbol name "SB-SIMD-AVX512F")))
                        (and s (fboundp s))))
                    '("U32.16" "MAKE-U32.16" "U32.16-SAP-REF" "U32.16-SAP-REF-MASKED"
                      "U32.16-SAP-REF-MASKED-Z" "U32.16-AND" "U32.16-ANDC1" "U32.16-OR"
                      "U32.16-XOR" "U32.16-NOT" "U32.16+" "U32.16-" "U32.16*"
                      "U32.16-SHIFTL" "U32.16-SHIFTR"))
             (find-symbol "INSTRUCTION-SET-AVAILABLE-P" "SB-SIMD-INTERNALS"))
    (pushnew :garnet-wl-avx512 *features*)))

#+garnet-wl-avx512
(progn

(defmacro px-simd-dispatch-function ((fn) &body body)
  "As PX-DISPATCH-FUNCTION, with OP on 16 pixels at a time."
  `(ecase ,fn
     ,@(loop for code from 0 to 15
             for form in '((sb-simd-avx512f:u32.16 0)
                           (sb-simd-avx512f:u32.16-and src dst)
                           (sb-simd-avx512f:u32.16-andc1 dst src)
                           src
                           (sb-simd-avx512f:u32.16-andc1 src dst)
                           dst
                           (sb-simd-avx512f:u32.16-xor src dst)
                           (sb-simd-avx512f:u32.16-or src dst)
                           (sb-simd-avx512f:u32.16-not (sb-simd-avx512f:u32.16-or src dst))
                           (sb-simd-avx512f:u32.16-not (sb-simd-avx512f:u32.16-xor src dst))
                           (sb-simd-avx512f:u32.16-not dst)
                           (sb-simd-avx512f:u32.16-or src (sb-simd-avx512f:u32.16-not dst))
                           (sb-simd-avx512f:u32.16-not src)
                           (sb-simd-avx512f:u32.16-or (sb-simd-avx512f:u32.16-not src) dst)
                           (sb-simd-avx512f:u32.16-not (sb-simd-avx512f:u32.16-and src dst))
                           (sb-simd-avx512f:u32.16 #xFFFFFFFF))
             collect `(,code (macrolet ((op (src dst)
                                          `(let ((src ,src) (dst ,dst))
                                             (declare (ignorable src dst))
                                             ,',form)))
                               ,@body)))))

(declaim (inline px-tail-mask))
(defun px-tail-mask (n)
  (declare (type (integer 0 16) n))
  (ldb (byte 16 0) (1- (ash 1 n))))

(defun px-row-op-avx512 (dpix di spix si n fn mask)
  (declare (type px-pixels dpix spix) (type fixnum di si n fn)
           (type (unsigned-byte 32) mask)
           (optimize (speed 3) (safety 0)))
  (if (/= mask #xFFFFFF)
      (px-row-op-scalar dpix di spix si n fn mask)
      (sb-sys:with-pinned-objects (dpix spix)
        (let ((dsap (sb-sys:vector-sap dpix))
              (ssap (sb-sys:vector-sap spix))
              (m (sb-simd-avx512f:u32.16 #xFFFFFF))
              (whole (* 16 (floor n 16))))
          (declare (type fixnum whole))
          (px-simd-dispatch-function (fn)
            (loop for i of-type fixnum from 0 below whole by 16
                  do (setf (sb-simd-avx512f:u32.16-sap-ref dsap (+ di i))
                           (sb-simd-avx512f:u32.16-and
                            m (op (sb-simd-avx512f:u32.16-sap-ref ssap (+ si i))
                                  (sb-simd-avx512f:u32.16-sap-ref dsap (+ di i))))))
            (let ((rest (- n whole)))
              (when (plusp rest)
                (let ((k (px-tail-mask rest)))
                  (setf (sb-simd-avx512f:u32.16-sap-ref-masked k dsap (+ di whole))
                        (sb-simd-avx512f:u32.16-and
                         m (op (sb-simd-avx512f:u32.16-sap-ref-masked-z k ssap (+ si whole))
                               (sb-simd-avx512f:u32.16-sap-ref-masked-z k dsap (+ di whole)))))))))))))

(defun px-row-fill-avx512 (dpix di n pixel fn mask)
  (declare (type px-pixels dpix) (type fixnum di n fn)
           (type (unsigned-byte 32) pixel mask)
           (optimize (speed 3) (safety 0)))
  (if (/= mask #xFFFFFF)
      (px-row-fill-scalar dpix di n pixel fn mask)
      (sb-sys:with-pinned-objects (dpix)
        (let ((dsap (sb-sys:vector-sap dpix))
              (s (sb-simd-avx512f:u32.16 pixel))
              (m (sb-simd-avx512f:u32.16 #xFFFFFF))
              (whole (* 16 (floor n 16))))
          (declare (type fixnum whole))
          (px-simd-dispatch-function (fn)
            (loop for i of-type fixnum from 0 below whole by 16
                  do (setf (sb-simd-avx512f:u32.16-sap-ref dsap (+ di i))
                           (sb-simd-avx512f:u32.16-and
                            m (op s (sb-simd-avx512f:u32.16-sap-ref dsap (+ di i))))))
            (let ((rest (- n whole)))
              (when (plusp rest)
                (let ((k (px-tail-mask rest)))
                  (setf (sb-simd-avx512f:u32.16-sap-ref-masked k dsap (+ di whole))
                        (sb-simd-avx512f:u32.16-and
                         m (op s (sb-simd-avx512f:u32.16-sap-ref-masked-z
                                  k dsap (+ di whole)))))))))))))

(defun px-row-blend-avx512 (dpix di alpha ai n colour)
  "As PX-ROW-BLEND: each channel becomes (a*fg + (255-a)*dst) / 255, rounded
down, which (t + 1 + (t >> 8)) >> 8 is exactly for t up to 255*255."
  (declare (type px-pixels dpix) (type (simple-array (unsigned-byte 8) (*)) alpha)
           (type fixnum di ai n) (type (unsigned-byte 32) colour)
           (optimize (speed 3) (safety 0)))
  (macrolet ((u (x) `(sb-simd-avx512f:u32.16 ,x)))
    (let ((fr (u (ldb (byte 8 16) colour)))
          (fg (u (ldb (byte 8 8) colour)))
          (fb (u (ldb (byte 8 0) colour)))
          (c255 (u 255)) (c1 (u 1)) (c8 (u 8)) (c16 (u 16)))
      (flet ((alphas (start count)
               ;; No byte-to-dword widening load in sb-simd: gather the
               ;; 16 coverages one by one.
               (declare (type fixnum start count))
               (macrolet ((a (k) `(if (< ,k count) (aref alpha (+ start ,k)) 0)))
                 (sb-simd-avx512f:make-u32.16
                  (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7)
                  (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15))))
             (blend (a d)
               (let ((na (sb-simd-avx512f:u32.16- c255 a)))
                 (flet ((channel (f shift)
                          (let* ((dc (sb-simd-avx512f:u32.16-and
                                      c255 (sb-simd-avx512f:u32.16-shiftr d shift)))
                                 (tt (sb-simd-avx512f:u32.16+
                                      (sb-simd-avx512f:u32.16* a f)
                                      (sb-simd-avx512f:u32.16* na dc))))
                            (sb-simd-avx512f:u32.16-shiftr
                             (sb-simd-avx512f:u32.16+ tt c1 (sb-simd-avx512f:u32.16-shiftr tt c8))
                             c8))))
                   (sb-simd-avx512f:u32.16-or
                    (sb-simd-avx512f:u32.16-shiftl (channel fr c16) c16)
                    (sb-simd-avx512f:u32.16-shiftl (channel fg c8) c8)
                    (channel fb (u 0)))))))
        (declare (inline alphas blend))
        (sb-sys:with-pinned-objects (dpix)
          (let ((dsap (sb-sys:vector-sap dpix))
                (whole (* 16 (floor n 16))))
            (declare (type fixnum whole))
            (loop for i of-type fixnum from 0 below whole by 16
                  do (setf (sb-simd-avx512f:u32.16-sap-ref dsap (+ di i))
                           (blend (alphas (+ ai i) 16)
                                  (sb-simd-avx512f:u32.16-sap-ref dsap (+ di i)))))
            (let ((rest (- n whole)))
              (when (plusp rest)
                (let ((k (px-tail-mask rest)))
                  (setf (sb-simd-avx512f:u32.16-sap-ref-masked k dsap (+ di whole))
                        (blend (alphas (+ ai whole) rest)
                               (sb-simd-avx512f:u32.16-sap-ref-masked-z
                                k dsap (+ di whole)))))))))))))

(defun px-install-avx512-kernels ()
  "Use the AVX-512 kernels if this CPU has AVX-512F."
  (when (sb-simd-internals:instruction-set-available-p
         (sb-simd-internals:find-instruction-set :avx512f))
    (setf *px-row-op* #'px-row-op-avx512
          *px-row-fill* #'px-row-fill-avx512
          *px-row-blend* #'px-row-blend-avx512)
    t))

(px-install-avx512-kernels)

) ; #+garnet-wl-avx512
