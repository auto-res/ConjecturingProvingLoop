

theorem P1_closed_complement {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P1 Aᶜ := by
  simpa using (open_implies_P1 hA.isOpen_compl)

theorem P1_image_of_continuous_open_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {f : X → Y} (hf : Continuous f) (hf_open : IsOpenMap f) (hA : Topology.P1 A) : Topology.P1 (f '' A) := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  have hx_cl : x ∈ closure (interior (A : Set X)) := hA hxA
  -- First, show `f x ∈ closure (f '' interior A)`.
  have h1 : f x ∈ closure (f '' interior (A : Set X)) := by
    apply (mem_closure_iff).2
    intro V hV_open hxV
    have h_pre_open : IsOpen (f ⁻¹' V) := hV_open.preimage hf
    have hx_pre : x ∈ f ⁻¹' V := by
      simpa using hxV
    rcases
        (mem_closure_iff).1 hx_cl (f ⁻¹' V) h_pre_open hx_pre with
      ⟨z, hz_pre, hz_int⟩
    refine ⟨f z, ?_⟩
    have hzV : f z ∈ V := by
      simpa using hz_pre
    have hz_img : f z ∈ f '' interior (A : Set X) := ⟨z, hz_int, rfl⟩
    exact And.intro hzV hz_img
  -- `f '' interior A` is open and sits inside `f '' A`.
  have h_open : IsOpen (f '' interior (A : Set X)) := by
    simpa using hf_open _ isOpen_interior
  have h_subset_img :
      (f '' interior (A : Set X) : Set Y) ⊆ f '' A := by
    intro z hz
    rcases hz with ⟨u, hu_int, rfl⟩
    exact ⟨u, interior_subset hu_int, rfl⟩
  have h_subset_int :
      (f '' interior (A : Set X) : Set Y) ⊆ interior (f '' A) :=
    interior_maximal h_subset_img h_open
  have h_closure_subset :
      closure (f '' interior (A : Set X)) ⊆ closure (interior (f '' A)) :=
    closure_mono h_subset_int
  exact h_closure_subset h1