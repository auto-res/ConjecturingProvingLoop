

theorem P3_compl_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P3 (Aᶜ) := by
  simpa using (P3_of_open (A := Aᶜ) hA.isOpen_compl)

theorem P2_iUnion_directed {X : Type*} [TopologicalSpace X] {ι : Type*} {s : ι → Set X} (hdir : Directed (· ⊆ ·) s) (h : ∀ i, P2 (s i)) : P2 (⋃ i, s i) := by
  simpa using (P2_iUnion (s := s) h)