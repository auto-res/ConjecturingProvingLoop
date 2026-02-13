

theorem P1_univ_iff {X : Type*} [TopologicalSpace X] : Topology.P1 (Set.univ : Set X) ↔ True := by
  constructor
  · intro _; trivial
  · intro _; exact Topology.P1_of_open (A := (Set.univ : Set X)) isOpen_univ

theorem P2_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {B : Set Y} (hB : IsOpen B) : Topology.P2 (f ⁻¹' B) := by
  -- The preimage of an open set under a continuous map is open.
  have hOpen : IsOpen (f ⁻¹' B) := hB.preimage hf
  -- Open sets satisfy `P2`.
  exact Topology.P2_of_open (A := f ⁻¹' B) hOpen