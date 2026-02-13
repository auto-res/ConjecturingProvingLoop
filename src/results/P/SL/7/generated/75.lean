

theorem Topology.P1_singleton_iff_isOpen_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {x : X} :
    Topology.P1 ({x} : Set X) ↔ IsOpen ({x} : Set X) := by
  constructor
  · intro hP1
    -- First, show that `interior {x}` is non-empty.
    have hIntNonempty : (interior ({x} : Set X)).Nonempty := by
      classical
      by_contra hEmpty
      have hIntEq : interior ({x} : Set X) = (∅ : Set X) := by
        simpa [Set.not_nonempty_iff_eq_empty] using hEmpty
      have hClosureEq : closure (interior ({x} : Set X)) = (∅ : Set X) := by
        simpa [hIntEq] using (closure_empty : closure (∅ : Set X) = (∅ : Set X))
      have hx_cl : (x : X) ∈ closure (interior ({x} : Set X)) := by
        have : (x : X) ∈ ({x} : Set X) := by
          simp
        exact hP1 this
      have : (x : X) ∈ (∅ : Set X) := by
        simpa [hClosureEq] using hx_cl
      exact this
    -- Obtain a point of the interior; it must be `x`.
    rcases hIntNonempty with ⟨y, hy⟩
    have hysingleton : y = x := by
      have : y ∈ ({x} : Set X) := (interior_subset : interior ({x} : Set X) ⊆ {x}) hy
      simpa [Set.mem_singleton_iff] using this
    have hxInt : (x : X) ∈ interior ({x} : Set X) := by
      simpa [hysingleton] using hy
    -- Hence `interior {x} = {x}`.
    have hSubset : ({x} : Set X) ⊆ interior ({x} : Set X) := by
      intro z hz
      have : z = x := by
        simpa [Set.mem_singleton_iff] using hz
      simpa [this] using hxInt
    have hIntEq : interior ({x} : Set X) = ({x} : Set X) := by
      apply Set.Subset.antisymm
      · exact interior_subset
      · exact hSubset
    -- Therefore `{x}` is open.
    have : IsOpen (interior ({x} : Set X)) := isOpen_interior
    simpa [hIntEq] using this
  · intro hOpen
    exact Topology.IsOpen_P1 (A := ({x} : Set X)) hOpen