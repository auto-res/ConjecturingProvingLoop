

theorem exists_dense_open_closed_P3 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, IsOpen A ∧ IsClosed A ∧ Dense A ∧ Topology.P3 A := by
  refine ⟨(Set.univ : Set X), isOpen_univ, isClosed_univ, dense_univ, ?_⟩
  simpa using Topology.P3_univ (X := X)

theorem P3_prod_five {U V W X Y : Type*} [TopologicalSpace U] [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] {A : Set U} {B : Set V} {C : Set W} {D : Set X} {E : Set Y} (hA : Topology.P3 A) (hB : Topology.P3 B) (hC : Topology.P3 C) (hD : Topology.P3 D) (hE : Topology.P3 E) : Topology.P3 (Set.prod (Set.prod (Set.prod (Set.prod A B) C) D) E) := by
  -- First, obtain `P3` for the fourfold product `(((A ×ˢ B) ×ˢ C) ×ˢ D)`.
  have hABCD : Topology.P3 (Set.prod (Set.prod (Set.prod A B) C) D) :=
    Topology.P3_prod_four
      (A := A) (B := B) (C := C) (D := D)
      hA hB hC hD
  -- Combine this with `E` to get the required fivefold product.
  simpa using
    (Topology.P3_prod
        (A := Set.prod (Set.prod (Set.prod A B) C) D)
        (B := E)
        hABCD hE)