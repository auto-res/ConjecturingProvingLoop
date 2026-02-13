

theorem Topology.disjoint_closure_interior_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Disjoint (closure (A : Set X)) (interior (Aᶜ : Set X)) := by
  refine Set.disjoint_left.2 ?_
  intro x hxCl hxInt
  -- `interior (Aᶜ)` is an open neighbourhood of `x`.
  have hOpen : IsOpen (interior (Aᶜ : Set X)) := isOpen_interior
  -- Since `x ∈ closure A`, this neighbourhood meets `A`.
  have hNonempty :
      ((interior (Aᶜ : Set X)) ∩ (A : Set X)).Nonempty :=
    (mem_closure_iff).1 hxCl (interior (Aᶜ)) hOpen hxInt
  rcases hNonempty with ⟨y, hyInt, hyA⟩
  -- But `y ∈ interior (Aᶜ)` implies `y ∈ Aᶜ`, contradicting `y ∈ A`.
  have : (y : X) ∈ (Aᶜ : Set X) :=
    (interior_subset : interior (Aᶜ : Set X) ⊆ Aᶜ) hyInt
  exact this hyA