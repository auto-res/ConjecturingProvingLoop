

theorem Topology.disjoint_interior_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Disjoint (interior (A : Set X)) (closure (Aᶜ : Set X)) := by
  refine Set.disjoint_left.2 ?_
  intro x hxInt hxCl
  -- `interior A` is an open neighbourhood of `x`.
  have hOpen : IsOpen (interior (A : Set X)) := isOpen_interior
  -- Since `x ∈ closure (Aᶜ)`, this neighbourhood meets `Aᶜ`.
  have hNon :
      ((interior (A : Set X)) ∩ (Aᶜ : Set X)).Nonempty :=
    (mem_closure_iff).1 hxCl (interior A) hOpen hxInt
  rcases hNon with ⟨y, hyInt, hyComp⟩
  -- But `y ∈ interior A ⊆ A`, contradicting `y ∈ Aᶜ`.
  have : (y : X) ∈ A := interior_subset hyInt
  exact hyComp this