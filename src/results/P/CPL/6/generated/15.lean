

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → Topology.P1 (closure A) := by
  intro hP1
  intro x hx_closure
  -- We will use the characterisation of closure via open neighbourhoods.
  have hgoal :
      ∀ U : Set X, IsOpen U → x ∈ U → (U ∩ interior (closure A)).Nonempty := by
    intro U hU hxU
    -- Since `x ∈ closure A`, the open set `U` meets `A`.
    have hUA_nonempty : (U ∩ (A : Set X)).Nonempty := by
      have hmem := (mem_closure_iff).1 hx_closure
      exact hmem U hU hxU
    rcases hUA_nonempty with ⟨y, hyU, hyA⟩
    -- Apply `P1` to the point `y ∈ A`.
    have hy_cl : y ∈ closure (interior A) := hP1 hyA
    -- Therefore `U` meets `interior A`.
    have hU_intA_nonempty : (U ∩ interior A).Nonempty := by
      have hmem_y := (mem_closure_iff).1 hy_cl
      exact hmem_y U hU hyU
    rcases hU_intA_nonempty with ⟨z, hzU, hzIntA⟩
    -- `interior A ⊆ interior (closure A)`.
    have hzIntClA : z ∈ interior (closure A) := by
      have hsubset : interior A ⊆ interior (closure A) :=
        interior_mono (subset_closure : (A : Set X) ⊆ closure A)
      exact hsubset hzIntA
    exact ⟨z, hzU, hzIntClA⟩
  exact (mem_closure_iff).2 hgoal

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : Topology.P1 A := by
  intro x hx
  simpa [h] using (Set.mem_univ x)

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : Topology.P2 A := by
  intro x hx
  simpa [h, interior_univ] using (Set.mem_univ x)

theorem P2_iff_P3_of_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A = closure (interior A)) : Topology.P2 A ↔ Topology.P3 A := by
  -- Equality of the relevant interiors obtained from the hypothesis on closures
  have h_int_eq : interior (closure A) = interior (closure (interior A)) := by
    simpa using congrArg interior h
  -- Prove the two implications
  constructor
  · intro hP2
    -- `P2 A → P3 A`
    intro x hxA
    have hx : x ∈ interior (closure (interior A)) := hP2 hxA
    simpa [h_int_eq] using hx
  · intro hP3
    -- `P3 A → P2 A`
    intro x hxA
    have hx : x ∈ interior (closure A) := hP3 hxA
    simpa [h_int_eq] using hx