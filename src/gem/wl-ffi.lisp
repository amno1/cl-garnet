;;; -*- Mode: LISP; Syntax: Common-Lisp; Package: GEM; Base: 10 -*-
;;;
;;; The few POSIX calls the Wayland backend needs that Wayflan does not
;;; provide: shared memory for wl_shm buffers and the keymap, poll(2) to
;;; wait on the display socket with a timeout, and a pipe that wakes the
;;; event loop when a timer thread queues an event.
;;;

(in-package :gem)

(cffi:defcfun ("memfd_create" %wl-memfd-create) :int
  (name :string) (flags :unsigned-int))

(cffi:defcfun ("ftruncate" %wl-ftruncate) :int
  (fd :int) (length :long))

(cffi:defcfun ("mmap" %wl-mmap) :pointer
  (addr :pointer) (length :size) (prot :int) (flags :int) (fd :int) (offset :long))

(cffi:defcfun ("munmap" %wl-munmap) :int
  (addr :pointer) (length :size))

(cffi:defcfun ("close" %wl-close) :int
  (fd :int))

(cffi:defcfun ("pipe" %wl-pipe) :int
  (fds :pointer))

(cffi:defcfun ("fcntl" %wl-fcntl) :int
  (fd :int) (cmd :int) (arg :int))

(cffi:defcfun ("read" %wl-read) :long
  (fd :int) (buf :pointer) (count :size))

(cffi:defcfun ("write" %wl-write) :long
  (fd :int) (buf :pointer) (count :size))

(cffi:defcfun ("poll" %wl-poll) :int
  (fds :pointer) (nfds :unsigned-long) (timeout :int))

(cffi:defcfun ("memcpy" %wl-memcpy) :pointer
  (dest :pointer) (src :pointer) (n :size))

(defconstant +wl-prot-read+ 1)
(defconstant +wl-prot-write+ 2)
(defconstant +wl-map-shared+ 1)
(defconstant +wl-map-private+ 2)
(defconstant +wl-mfd-cloexec+ 1)
(defconstant +wl-f-setfl+ 4)
(defconstant +wl-o-nonblock+ #o4000)
(defconstant +wl-pollin+ 1)

(defun wl-map-failed-p (pointer)
  ;; MAP_FAILED is (void *) -1.
  (= (cffi:pointer-address pointer)
     (ldb (byte (* 8 (cffi:foreign-type-size :pointer)) 0) -1)))

(defun wl-make-shm (size)
  "Make an anonymous shared memory file of SIZE bytes and map it.
Returns (VALUES FD POINTER)."
  (let ((fd (%wl-memfd-create "garnet-wl" +wl-mfd-cloexec+)))
    (when (minusp fd)
      (error "Wayland backend: memfd_create failed"))
    (when (minusp (%wl-ftruncate fd size))
      (%wl-close fd)
      (error "Wayland backend: ftruncate of ~D bytes failed" size))
    (let ((ptr (%wl-mmap (cffi:null-pointer) size
                         (logior +wl-prot-read+ +wl-prot-write+)
                         +wl-map-shared+ fd 0)))
      (when (wl-map-failed-p ptr)
        (%wl-close fd)
        (error "Wayland backend: mmap of ~D bytes failed" size))
      (values fd ptr))))

(defun wl-make-wake-pipe ()
  "Return (VALUES READ-FD WRITE-FD) of a pipe whose ends do not block."
  (cffi:with-foreign-object (fds :int 2)
    (when (minusp (%wl-pipe fds))
      (error "Wayland backend: pipe failed"))
    (let ((r (cffi:mem-aref fds :int 0))
          (w (cffi:mem-aref fds :int 1)))
      (%wl-fcntl r +wl-f-setfl+ +wl-o-nonblock+)
      (%wl-fcntl w +wl-f-setfl+ +wl-o-nonblock+)
      (values r w))))

(defun wl-poke-pipe (fd)
  (cffi:with-foreign-object (b :uint8)
    (setf (cffi:mem-ref b :uint8) 1)
    (%wl-write fd b 1)))

(defun wl-drain-pipe (fd)
  (cffi:with-foreign-object (b :uint8 64)
    (loop while (plusp (%wl-read fd b 64)))))

(defun wl-poll-fds (fds timeout-ms)
  "Wait until one of FDS can be read, or TIMEOUT-MS milliseconds pass
(forever if NIL).  Returns the list of FDS that can be read."
  (let ((n (length fds)))
    ;; struct pollfd { int fd; short events; short revents; }
    (cffi:with-foreign-object (p :uint8 (* 8 n))
      (loop for fd in fds
            for i from 0
            do (setf (cffi:mem-ref p :int (* 8 i)) fd
                     (cffi:mem-ref p :short (+ 4 (* 8 i))) +wl-pollin+
                     (cffi:mem-ref p :short (+ 6 (* 8 i))) 0))
      (let ((r (%wl-poll p n (if timeout-ms (max 0 (round timeout-ms)) -1))))
        (if (plusp r)
            (loop for fd in fds
                  for i from 0
                  unless (zerop (cffi:mem-ref p :short (+ 6 (* 8 i))))
                    collect fd)
            nil)))))
