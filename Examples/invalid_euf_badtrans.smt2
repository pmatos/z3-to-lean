; Invalid proof - EUF with non-transitive equality
; Claims a = c from a = b and unrelated premises
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun d () Int)

(define-const $1 Bool (= a b))
(assume $1)

(define-const $2 Bool (= c d))
(assume $2)

; Try to claim a = c which doesn't follow
(declare-fun euf (Bool Bool Bool) Proof)
(define-const $3 Bool (= a c))
(define-const $4 Proof (euf $3 $1 $2))
(infer (not $1) (not $2) $3 $4)
