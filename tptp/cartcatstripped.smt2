(declare-sort Gat 0)
(declare-fun compose (Gat Gat) Gat)
(declare-fun id (Gat) Gat)
(declare-fun otimes (Gat Gat) Gat)
(declare-fun munit () Gat)
(declare-fun braid (Gat Gat) Gat)
(declare-fun mcopy (Gat) Gat)
(declare-fun delete (Gat) Gat)
(declare-fun pair (Gat Gat) Gat)
(declare-fun proj1 (Gat Gat) Gat)
(declare-fun proj2 (Gat Gat) Gat)
(declare-fun B () Gat)
(declare-fun A () Gat)
(assert (forall ((A Gat) (B Gat) (C Gat) (D Gat) (f Gat) (g Gat) (h Gat))
  (= (compose (compose f g) h) (compose f (compose g h)))))
;(assert (forall ((A Gat) (B Gat) (f Gat)) (= (compose f (id B)) f)))
;(assert (forall ((A Gat) (B Gat) (f Gat)) (= (compose (id A) f) f)))
;(assert (forall ((A Gat) (B Gat) (C Gat))
;  (= (otimes (otimes A B) C) (otimes A (otimes B C)))))
;(assert (forall ((A Gat)) (= (otimes A munit) A)))
; (assert (forall ((A Gat)) (= (otimes munit A) A)))
(assert (forall ((A Gat)
         (B Gat)
         (C Gat)
        (X Gat)
         (Y Gat)
         (Z Gat)
         (f Gat)
         (g Gat)
         (h Gat))
  (= (otimes (otimes f g) h) (otimes f (otimes g h)))))
(assert (forall ((A Gat)
         (B Gat)
         (C Gat)
         (X Gat)
         (Y Gat)
         (Z Gat)
         (f Gat)
         (h Gat)
         (g Gat)
         (k Gat))
  (= (compose (otimes f g) (otimes h k)) (otimes (compose f h) (compose g k)))))
(assert (forall ((A Gat) (B Gat)) (= (id (otimes A B)) (otimes (id A) (id B)))))
(assert (forall ((A Gat) (B Gat))
  (= (compose (braid A B) (braid B A)) (id (otimes A B)))))
(assert (forall ((A Gat) (B Gat) (C Gat))
  (= (braid A (otimes B C))
     (compose (otimes (braid A B) (id C)) (otimes (id B) (braid A C))))))
(assert (forall ((A Gat) (B Gat) (C Gat))
  (= (braid (otimes A B) C)
     (compose (otimes (id A) (braid B C)) (otimes (braid A C) (id B))))))
(assert (forall ((A Gat) (B Gat) (C Gat) (D Gat) (f Gat) (g Gat))
  (= (compose (otimes f g) (braid B D)) (compose (braid A C) (otimes g f)))))
(assert (forall ((A Gat))
  (= (compose (mcopy A) (otimes (mcopy A) (id A)))
     (compose (mcopy A) (otimes (id A) (mcopy A))))))
(assert (forall ((A Gat)) (= (compose (mcopy A) (otimes (delete A) (id A))) (id A))))
(assert (forall ((A Gat)) (= (compose (mcopy A) (otimes (id A) (delete A))) (id A))))
(assert (forall ((A Gat)) (= (compose (mcopy A) (braid A A)) (mcopy A))))
(assert (forall ((A Gat) (B Gat))
  (let ((a!1 (compose (otimes (mcopy A) (mcopy B))
                      (otimes (otimes (id A) (braid A B)) (id B)))))
    (= (mcopy (otimes A B)) a!1))))
(assert (forall ((A Gat) (B Gat))
  (= (delete (otimes A B)) (otimes (delete A) (delete B)))))
(assert (= (mcopy munit) (id munit)))
(assert (= (delete munit) (id munit)))
(assert (forall ((A Gat) (B Gat) (C Gat) (f Gat) (g Gat))
  (= (pair f g) (compose (mcopy C) (otimes f g)))))
(assert (forall ((A Gat) (B Gat)) (= (proj1 A B) (otimes (id A) (delete B)))))
(assert (forall ((A Gat) (B Gat)) (= (proj2 A B) (otimes (delete A) (id B)))))
(assert (forall ((A Gat) (B Gat) (f Gat))
  (= (compose f (mcopy B)) (compose (mcopy A) (otimes f f)))))
(assert (forall ((A Gat) (B Gat) (f Gat)) (= (compose f (delete B)) (delete A))))
(assert (not (= (pair (proj1 A B) (proj2 A B)) (otimes (id A) (id B)))))
(check-sat)

;right. This is obviously shit