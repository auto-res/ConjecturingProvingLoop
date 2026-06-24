

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (A := A) → Topology.P1 (X := X) (A := A) :=
by
  dsimp [Topology.P2, Topology.P1]
  intro hP2 x hxA
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  exact interior_subset hx_int