

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → P1 (closure A) := by
  intro hP1
  unfold P1 at hP1 ⊢
  intro x hx
  -- show that every neighborhood of `x` meets `interior (closure A)`
  apply (mem_closure_iff).2
  intro U hU hxU
  -- since `x ∈ closure A`, `U` meets `A`
  have hUA : (U ∩ A).Nonempty := by
    have := (mem_closure_iff).1 hx U hU hxU
    simpa using this
  rcases hUA with ⟨y, hyU, hyA⟩
  -- from `P1 A` we know `y ∈ closure (interior A)`
  have hy_clos : y ∈ closure (interior A) := hP1 hyA
  -- hence `U` meets `interior A`
  have hU_intA : (U ∩ interior A).Nonempty := by
    have := (mem_closure_iff).1 hy_clos U hU hyU
    simpa using this
  rcases hU_intA with ⟨z, hzU, hzIntA⟩
  -- but `interior A ⊆ interior (closure A)`
  have hzIntClA : z ∈ interior (closure A) :=
    (interior_mono subset_closure) hzIntA
  exact ⟨z, hzU, hzIntClA⟩