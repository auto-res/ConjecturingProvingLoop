

theorem P3_of_open_with_same_closure {X : Type*} [TopologicalSpace X] {A U : Set X} (hUopen : IsOpen U) (hAU : A ⊆ U) (hClos : closure U = closure A) : Topology.P3 A := by
  intro x hxA
  have hxU : x ∈ U := hAU hxA
  have hP3U : P3 U := P3_of_open hUopen
  have hInt : x ∈ interior (closure U) := hP3U hxU
  simpa [hClos] using hInt

theorem exists_open_subset_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hP3 : Topology.P3 A) : ∃ U, IsOpen U ∧ A ⊆ U ∧ U ⊆ interior (closure A) := by
  refine ⟨interior (closure (A : Set X)), isOpen_interior, ?_, subset_refl _⟩
  intro x hxA
  exact hP3 hxA

theorem P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P3 (closure A)) : Topology.P3 A := by
  intro x hxA
  have hx_closure : x ∈ closure (A : Set X) := subset_closure hxA
  have hx_int : x ∈ interior (closure (closure (A : Set X))) := h hx_closure
  simpa [closure_closure] using hx_int