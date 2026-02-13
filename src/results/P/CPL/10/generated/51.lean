

theorem P1_compl_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P1 (Aᶜ) := by
  simpa using
    (Topology.P1_of_open (X := X) (A := Aᶜ) hA.isOpen_compl)

theorem exists_nowhere_dense_P2 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, closure A = A ∧ interior A = (∅ : Set X) ∧ Topology.P2 A := by
  refine ⟨(∅ : Set X), ?_, ?_, ?_⟩
  · simp
  · simp
  · exact Topology.P2_empty (X := X)

theorem P2_prod_five {V W X Y Z : Type*} [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set V} {B : Set W} {C : Set X} {D : Set Y} {E : Set Z} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) (hD : Topology.P2 D) (hE : Topology.P2 E) : Topology.P2 (Set.prod (Set.prod (Set.prod (Set.prod A B) C) D) E) := by
  -- First, obtain `P2` for the triple product `(A ×ˢ B) ×ˢ C`.
  have hABC : Topology.P2 (Set.prod (Set.prod A B) C) :=
    Topology.P2_prod_three (A := A) (B := B) (C := C) hA hB hC
  -- Combine with `D` to get a fourfold product.
  have hABCD : Topology.P2 (Set.prod (Set.prod (Set.prod A B) C) D) :=
    Topology.P2_prod (A := Set.prod (Set.prod A B) C) (B := D) hABC hD
  -- Finally, combine with `E` to obtain the desired fivefold product.
  simpa using
    (Topology.P2_prod
        (A := Set.prod (Set.prod (Set.prod A B) C) D) (B := E)
        hABCD hE)

theorem P2_union_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {F : ι → Set X} (hF : ∀ i, Topology.P2 (F i)) : Topology.P2 (⋃ i, F i) := by
  simpa using (Topology.P2_iUnion (X := X) (F := F) hF)

theorem exists_open_dense_P1 {X : Type*} [TopologicalSpace X] : ∃ U : Set X, IsOpen U ∧ Dense U ∧ Topology.P1 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, dense_univ, ?_⟩
  simpa using Topology.P1_univ (X := X)