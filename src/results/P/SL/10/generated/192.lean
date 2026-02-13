

theorem Topology.closure_diff_subset_closure_diff {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A \ B) ⊆ closure A \ interior B := by
  intro x hx
  -- First, `x` lies in the closure of `A`.
  have hxClA : x ∈ closure A :=
    (closure_mono (Set.diff_subset : A \ B ⊆ A)) hx
  -- Next, show that `x ∉ interior B`.
  have hxNotIntB : x ∉ interior B := by
    intro hxIntB
    -- Since `x ∈ closure (A \ B)`, every neighbourhood of `x` meets `A \ B`.
    have h_nonempty :
        (interior B ∩ (A \ B)).Nonempty := by
      have h_open : IsOpen (interior B) := isOpen_interior
      exact (mem_closure_iff).1 hx (interior B) h_open hxIntB
    rcases h_nonempty with ⟨y, hyIntB, hyDiff⟩
    -- But `y ∈ interior B` implies `y ∈ B`, contradicting `y ∉ B`.
    have : y ∈ B := interior_subset hyIntB
    exact (hyDiff.2 this).elim
  exact And.intro hxClA hxNotIntB