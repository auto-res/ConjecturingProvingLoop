

theorem P2_imp_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 (A)) :
    Topology.P1 (A) ∧ Topology.P3 (A) := by
  refine And.intro ?P1 ?P3
  · -- Proof of P1
    unfold Topology.P1 Topology.P2 at *
    intro x hx
    have hx' : x ∈ interior (closure (interior A)) := hA hx
    have hsubset : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    exact hsubset hx'
  · -- Proof of P3
    unfold Topology.P3 Topology.P2 at *
    intro x hx
    have hx' : x ∈ interior (closure (interior A)) := hA hx
    have hsub_cl : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    have hsub_int : interior (closure (interior A)) ⊆ interior (closure A) :=
      interior_mono hsub_cl
    exact hsub_int hx'