

theorem P1_sdiff {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P1 A) (hB : IsClosed B) : Topology.P1 (A \ B) := by
  intro x hx
  -- Decompose the membership in `A \ B`.
  have hxA : x ∈ A := hx.1
  have hx_notB : x ∈ (Bᶜ : Set X) := by
    -- `hx.2 : x ∉ B`, which is definitionally `x ∈ Bᶜ`.
    simpa using hx.2
  -- We show that every neighbourhood of `x` meets `interior (A \ B)`.
  apply (mem_closure_iff).2
  intro V hV_open hxV
  -- Intersect the neighbourhood with `Bᶜ`, still an open neighbourhood of `x`.
  have hW_open : IsOpen (V ∩ (Bᶜ : Set X)) :=
    hV_open.inter hB.isOpen_compl
  have hxW : x ∈ V ∩ (Bᶜ : Set X) := And.intro hxV hx_notB
  -- Since `x ∈ closure (interior A)`, this set meets `interior A`.
  have hx_clA : x ∈ closure (interior A) := hA hxA
  rcases
      (mem_closure_iff).1 hx_clA _ hW_open hxW with
    ⟨y, hyW, hy_intA⟩
  -- Extract the two facts `y ∈ V` and `y ∈ Bᶜ`.
  have hyV : y ∈ V := hyW.1
  have hy_notB : y ∈ (Bᶜ : Set X) := hyW.2
  -- Show that `y` actually belongs to `interior (A \ B)`.
  have hy_int_diff : y ∈ interior (A \ B) := by
    -- The open set `interior A ∩ Bᶜ` sits inside `A \ B`.
    have h_subset :
        (interior A ∩ (Bᶜ : Set X) : Set X) ⊆ interior (A \ B) := by
      -- Basic inclusion into `A \ B`.
      have h_basic :
          (interior A ∩ (Bᶜ : Set X) : Set X) ⊆ (A \ B) := by
        intro z hz
        exact And.intro (interior_subset hz.1) hz.2
      -- Openness of the set.
      have h_open :
          IsOpen ((interior A) ∩ (Bᶜ : Set X) : Set X) :=
        (isOpen_interior.inter hB.isOpen_compl)
      -- Apply the maximality property of `interior`.
      exact interior_maximal h_basic h_open
    have hy_mem : y ∈ (interior A ∩ (Bᶜ : Set X)) := And.intro hy_intA hy_notB
    exact h_subset hy_mem
  -- Provide the desired witness in `V ∩ interior (A \ B)`.
  exact ⟨y, And.intro hyV hy_int_diff⟩

theorem P3_exists_open_dense {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 A → ∃ U, IsOpen U ∧ closure U ⊆ closure A ∧ interior (closure A) ⊆ closure U := by
  intro _hP3
  refine ⟨interior (closure (A : Set X)), isOpen_interior, ?_, ?_⟩
  · -- `closure U ⊆ closure A`
    have h_subset :
        (interior (closure (A : Set X)) : Set X) ⊆ closure A :=
      interior_subset
    -- Taking closures preserves inclusions.
    have h_closure :
        closure (interior (closure (A : Set X))) ⊆ closure A := by
      simpa [closure_closure] using (closure_mono h_subset)
    exact h_closure
  · -- `interior (closure A) ⊆ closure U`
    intro x hx
    exact subset_closure hx

theorem P1_iff {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ (∀ x, x ∉ closure (interior A) → x ∉ A) := by
  classical
  constructor
  · intro hP1 x hx_not hxA
    have hx_cl : x ∈ closure (interior (A : Set X)) := hP1 hxA
    exact hx_not hx_cl
  · intro hCond x hxA
    have hx_cl : x ∈ closure (interior (A : Set X)) := by
      by_cases hmem : x ∈ closure (interior (A : Set X))
      · exact hmem
      · have h_notA : x ∉ A := hCond x hmem
        exact (False.elim (h_notA hxA))
    exact hx_cl