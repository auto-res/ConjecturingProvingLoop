

theorem Topology.closure_inter_closure_compl_eq_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ∩ closure (Aᶜ) = frontier A := by
  ext x
  constructor
  · -- `→`  direction
    intro hx
    rcases hx with ⟨hxClosA, hxClosCompl⟩
    have hxNotInt : x ∉ interior A := by
      intro hInt
      -- Since `x ∈ closure (Aᶜ)`, every open neighbourhood of `x`
      -- meets `Aᶜ`. Taking `interior A`, we obtain a contradiction.
      have hNonempty :=
        (mem_closure_iff.1 hxClosCompl) (interior A) isOpen_interior hInt
      rcases hNonempty with ⟨y, ⟨hyInt, hyCompl⟩⟩
      have hyA : y ∈ A := interior_subset hyInt
      exact hyCompl hyA
    exact And.intro hxClosA hxNotInt
  · -- `←` direction
    intro hxFront
    have hxClosA : x ∈ closure A := hxFront.1
    have hxClosCompl : x ∈ closure (Aᶜ) :=
      (Topology.frontier_subset_closure_compl (A := A)) hxFront
    exact And.intro hxClosA hxClosCompl