

theorem P1_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A ↔ Topology.P2 A := by
  simpa using
    (P1_iff_P3_of_open (X := X) (A := A) hA).trans
      ((P2_iff_P3_of_open (A := A) hA).symm)

theorem P1_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P1 A) (hB : Topology.P1 B) (hC : Topology.P1 C) : Topology.P1 ((Set.prod A B).prod C) := by
  -- First, establish `P1` for `A × B`.
  have hAB : Topology.P1 (Set.prod A B) :=
    P1_prod (X := X) (Y := Y) (A := A) (B := B) hA hB
  -- Then use it together with `hC` to get `P1` for `(A × B) × C`.
  have hABC : Topology.P1 ((Set.prod A B).prod C) :=
    P1_prod (X := X × Y) (Y := Z) (A := Set.prod A B) (B := C) hAB hC
  simpa using hABC

theorem P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (closure (interior A)) := by
  -- `interior A` satisfies `P1`.
  have h : Topology.P1 (interior A) := P1_interior (X := X) (A := A)
  -- Hence its closure also satisfies `P1`.
  simpa using (P1_closure (X := X) (A := interior A) h)