

theorem P2_exists_open_superset {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P2 A) : ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ interior (closure (interior A)) := by
  refine
    ⟨interior (closure (interior A)), isOpen_interior, hA, subset_rfl⟩

theorem interior_closure_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 (interior (closure A)) := by
  dsimp [Topology.P2]
  intro x hx
  -- `interior (closure A)` is open and contained in its closure, hence in the
  -- interior of that closure.
  have h_incl :
      (interior (closure A) : Set X) ⊆
        interior (closure (interior (closure A))) :=
    interior_maximal
      (subset_closure :
        (interior (closure A) : Set X) ⊆ closure (interior (closure A)))
      isOpen_interior
  have : x ∈ interior (closure (interior (closure A))) := h_incl hx
  simpa [interior_interior] using this

theorem P2_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) : Topology.P2 (Set.prod A (Set.prod B C)) := by
  -- First, obtain `P2` for the product `B × C`.
  have hBC : Topology.P2 (Set.prod B C) := by
    simpa using (P2_prod (X := Y) (Y := Z) (A := B) (B := C) hB hC)
  -- Now, obtain `P2` for `A × (B × C)` using the previous result.
  simpa using
    (P2_prod (X := X) (Y := Y × Z) (A := A) (B := Set.prod B C) hA hBC)