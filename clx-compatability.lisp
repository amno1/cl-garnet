

(in-package :xlib)

;;; Some CLX releases (c. 2018) dropped these functions; current CLX defines
;;; them again, as structure predicates and accessors.  Define them only when
;;; missing: redefining a structure accessor is a full warning in SBCL, which
;;; fails the compile.  The DEFUNs are not at top level, so the compiler does
;;; not claim the names at compile time either.

(unless (fboundp 'pixmap-p)
  (defun pixmap-p (object)
    (typep object 'pixmap)))

(unless (fboundp 'image-z-p)
  (defun image-z-p (object)
    (typep object 'image-z)))

(export 'xlib::image-z-p :xlib)

(unless (fboundp 'pixmap-plist)
  (defun pixmap-plist (pixmap)
    (xlib:drawable-plist pixmap)))

(unless (fboundp '(setf pixmap-plist))
  (defun (setf pixmap-plist) (value window)
    (setf (drawable-plist window) value)))
