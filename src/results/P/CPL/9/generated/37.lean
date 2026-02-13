

theorem P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 (A := A) ↔ (Topology.P1 (A := A) ∧ Topology.P3 (A := A)) := by
  constructor
  · intro hP2
    exact P2_imp_P1_and_P3 (A := A) hP2
  · rintro ⟨hP1, hP3⟩
    exact P1_and_P3_imp_P2 (A := A) hP1 hP3

theorem P1_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P1 (A := A)) (hB : Topology.P1 (A := B)) (hC : Topology.P1 (A := C)) : Topology.P1 (A := Set.prod A (Set.prod B C)) := by
  -- First, obtain `P1` for `B × C` in the space `Y × Z`.
  have hBC : Topology.P1 (A := Set.prod B C) := by
    simpa using
      (Topology.P1_prod (A := B) (B := C) hB hC)
  -- Now combine `A` with `B × C`.
  simpa using
    (Topology.P1_prod (A := A) (B := Set.prod B C) hA hBC)

theorem P2_prod_three_univ_left {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {B : Set Y} {C : Set Z} (hB : Topology.P2 (A := B)) (hC : Topology.P2 (A := C)) : Topology.P2 (A := Set.prod (Set.univ : Set X) (Set.prod B C)) := by
  -- First, obtain `P2` for the product `B × C` in the space `Y × Z`.
  have hBC : Topology.P2 (A := Set.prod B C) := by
    simpa using
      (Topology.P2_product
        (X := Y) (Y := Z)
        (A := B) (B := C)
        (hA := hB) (hB := hC))
  -- Now combine `Set.univ` with `B × C`.
  simpa using
    (Topology.P2_product
      (X := X) (Y := Y × Z)
      (A := (Set.univ : Set X)) (B := Set.prod B C)
      (hA := Topology.P2_univ (X := X))
      (hB := hBC))

theorem P3_iff_P1_of_open_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h_open : IsOpen A) (h_dense : Dense A) : Topology.P3 (A := A) ↔ Topology.P1 (A := A) := by
  simpa using
    ((P2_iff_P3_of_open (A := A) h_open).symm.trans
      ((P1_iff_P2_of_dense (A := A) h_dense).symm))