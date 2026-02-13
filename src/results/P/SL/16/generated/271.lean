

theorem _root_.IsOpen.compl {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : IsClosed (Aᶜ) := by
  simpa [isClosed_compl_iff] using (isClosed_compl_iff).2 hA