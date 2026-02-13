

theorem Topology.interior_inter_closure_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∩ closure B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hxIntA, hxClB⟩
  -- We will use the characterization `mem_closure_iff`.
  -- It suffices to show that every open neighbourhood `U` of `x`
  -- meets `A ∩ B`.
  refine (mem_closure_iff).2 ?_
  intro U hUopen hxU
  -- Consider `U ∩ interior A`, an open neighbourhood of `x`
  -- contained in `A`.
  have hU_intA_open : IsOpen (U ∩ interior A) := hUopen.inter isOpen_interior
  have hxU_intA : x ∈ (U ∩ interior A) := And.intro hxU hxIntA
  -- Since `x ∈ closure B`, this neighbourhood intersects `B`.
  have h_nonempty : ((U ∩ interior A) ∩ B).Nonempty :=
    (mem_closure_iff.1 hxClB) (U ∩ interior A) hU_intA_open hxU_intA
  -- Extract a point `y` witnessing the intersection.
  rcases h_nonempty with ⟨y, ⟨hyU_intA, hyB⟩⟩
  -- From `y ∈ U ∩ interior A` we get `y ∈ U` and `y ∈ A`.
  have hyU : y ∈ U := hyU_intA.1
  have hyA : y ∈ A := interior_subset hyU_intA.2
  -- Thus `y ∈ U ∩ (A ∩ B)`, as required.
  exact ⟨y, And.intro hyU (And.intro hyA hyB)⟩