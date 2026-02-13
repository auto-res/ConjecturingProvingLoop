

theorem P2_diff {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 A) (hB : IsClosed B) : Topology.P2 (A \ B) := by
  intro x hx
  -- Decompose the membership `x ∈ A \ B`
  rcases hx with ⟨hxA, hx_notB⟩
  -- From `P2 A` we get that `x` belongs to `interior (closure (interior A))`
  have hx_int : (x : X) ∈ interior (closure (interior A)) := hA hxA
  -- Introduce an auxiliary open set
  set S : Set X := interior (closure (interior A)) ∩ Bᶜ with hS_def
  -- The set `S` is open
  have hS_open : IsOpen S := by
    have h₁ : IsOpen (interior (closure (interior A))) := isOpen_interior
    have h₂ : IsOpen (Bᶜ : Set X) := hB.isOpen_compl
    simpa [hS_def] using h₁.inter h₂
  -- Show that `S ⊆ closure (interior (A \ B))`
  have hS_subset : (S : Set X) ⊆ closure (interior (A \ B)) := by
    intro y hy
    rcases hy with ⟨hy_int, hy_notB⟩
    -- `y` is in the closure of `interior A`
    have hy_closure : y ∈ closure (interior A) := interior_subset hy_int
    -- We prove `y ∈ closure (interior (A \ B))` using `mem_closure_iff`
    have : y ∈ closure (interior (A \ B)) := by
      apply (mem_closure_iff).2
      intro o ho hy_o
      -- Consider the open neighbourhood `o ∩ Bᶜ`
      have hB_open : IsOpen (Bᶜ : Set X) := hB.isOpen_compl
      have ho₁_open : IsOpen (o ∩ Bᶜ) := ho.inter hB_open
      have hy_o₁ : y ∈ o ∩ Bᶜ := ⟨hy_o, hy_notB⟩
      -- Since `y ∈ closure (interior A)`, this open set meets `interior A`
      have h_meet : ((o ∩ Bᶜ) ∩ interior A).Nonempty := by
        have h_cond := (mem_closure_iff).1 hy_closure
        have h := h_cond (o ∩ Bᶜ) ho₁_open hy_o₁
        simpa [Set.inter_assoc, Set.inter_left_comm] using h
      rcases h_meet with ⟨w, ⟨hw_o, hw_notB⟩, hw_intA⟩
      -- Show that `w ∈ interior (A \ B)`
      have hU_open : IsOpen (interior A ∩ Bᶜ) :=
        (isOpen_interior).inter hB_open
      have hU_subset : (interior A ∩ Bᶜ : Set X) ⊆ A \ B := by
        intro z hz
        rcases hz with ⟨hz_intA, hz_notB⟩
        have hzA : z ∈ A := interior_subset hz_intA
        exact ⟨hzA, hz_notB⟩
      have hU_subset_int :
          (interior A ∩ Bᶜ : Set X) ⊆ interior (A \ B) :=
        interior_maximal hU_subset hU_open
      have hw_intAB : w ∈ interior (A \ B) :=
        hU_subset_int ⟨hw_intA, hw_notB⟩
      -- Hence `o` meets `interior (A \ B)`
      exact ⟨w, hw_o, hw_intAB⟩
    simpa using this
  -- `x` belongs to `S`
  have hxS : x ∈ S := by
    have hx_comp : x ∈ (Bᶜ : Set X) := by
      simp [hx_notB]
    simpa [hS_def] using And.intro hx_int hx_comp
  -- `S` is an open neighbourhood of `x` contained in the desired closure,
  -- hence `x` is in its interior
  have hx_target :
      (x : X) ∈ interior (closure (interior (A \ B))) :=
    (interior_maximal hS_subset hS_open) hxS
  exact hx_target

theorem P3_diff {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P3 A) (hB : IsClosed B) : Topology.P3 (A \ B) := by
  intro x hx
  rcases hx with ⟨hxA, hxNotB⟩
  -- `x` lies in the interior of the closure of `A`
  have hx_int : (x : X) ∈ interior (closure A) := hA hxA
  -- Define an auxiliary open set
  set S : Set X := interior (closure A) ∩ Bᶜ with hS_def
  -- `S` is open
  have hS_open : IsOpen S := by
    have h₁ : IsOpen (interior (closure A)) := isOpen_interior
    have h₂ : IsOpen (Bᶜ : Set X) := hB.isOpen_compl
    simpa [hS_def] using h₁.inter h₂
  -- `x` belongs to `S`
  have hxS : x ∈ S := by
    have : x ∈ interior (closure A) ∧ x ∈ Bᶜ := ⟨hx_int, hxNotB⟩
    simpa [hS_def] using this
  -- Show that `S ⊆ closure (A \ B)`
  have hS_subset : (S : Set X) ⊆ closure (A \ B) := by
    intro y hyS
    -- Decompose membership in `S`
    have hyInt_and_notB : y ∈ interior (closure A) ∧ y ∈ Bᶜ := by
      simpa [hS_def] using hyS
    have hy_int  := hyInt_and_notB.1
    have hy_notB := hyInt_and_notB.2
    -- Hence `y ∈ closure A`
    have hy_clA : y ∈ closure A := interior_subset hy_int
    -- Prove `y ∈ closure (A \ B)`
    have : y ∈ closure (A \ B) := by
      -- Use `mem_closure_iff`
      apply (mem_closure_iff).2
      intro V hVopen hyV
      -- Consider the open neighbourhood `V ∩ Bᶜ`
      have hVB_open : IsOpen (V ∩ Bᶜ) := hVopen.inter hB.isOpen_compl
      have hyVBC : y ∈ V ∩ Bᶜ := ⟨hyV, hy_notB⟩
      -- Since `y ∈ closure A`, this set meets `A`
      have h_nonempty : ((V ∩ Bᶜ) ∩ A).Nonempty := by
        have := (mem_closure_iff).1 hy_clA (V ∩ Bᶜ) hVB_open hyVBC
        simpa [Set.inter_assoc, Set.inter_left_comm] using this
      rcases h_nonempty with ⟨z, hz⟩
      rcases hz with ⟨⟨hzV, hzNotB⟩, hzA⟩
      have hz_in_diff : z ∈ A \ B := ⟨hzA, hzNotB⟩
      exact ⟨z, hzV, hz_in_diff⟩
    exact this
  -- Apply `interior_maximal` to obtain the desired inclusion
  have hS_int : (S : Set X) ⊆ interior (closure (A \ B)) :=
    interior_maximal hS_subset hS_open
  -- Conclude for the original point `x`
  exact hS_int hxS

theorem exists_closed_P2 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, IsClosed A ∧ Topology.P2 A := by
  exact ⟨(∅ : Set X), isClosed_empty, Topology.P2_empty (X := X)⟩

theorem exists_dense_P3_closed {X : Type*} [TopologicalSpace X] : ∃ A : Set X, IsClosed A ∧ Dense A ∧ Topology.P3 A := by
  refine ⟨(Set.univ : Set X), isClosed_univ, dense_univ, ?_⟩
  simpa using Topology.P3_univ (X := X)

theorem P1_subset_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → closure (interior A) ⊆ closure A := by
  intro _hP1
  exact closure_mono (interior_subset : (interior A : Set X) ⊆ A)

theorem P1_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P1 A) (hB : Topology.P1 B) (hC : Topology.P1 C) : Topology.P1 (Set.prod (Set.prod A B) C) := by
  -- First, use `hA` and `hB` to obtain `P1` for the product `A ×ˢ B`.
  have hAB : Topology.P1 (Set.prod A B) :=
    Topology.P1_prod (X := X) (Y := Y) (A := A) (B := B) hA hB
  -- Combine `hAB` with `hC` to get the desired result.
  simpa using
    (Topology.P1_prod
        (X := X × Y) (Y := Z)
        (A := Set.prod A B) (B := C)
        hAB hC)

theorem P2_iff_exists_open_subset {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A ↔ ∀ x ∈ A, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ interior (closure (interior A)) := by
  constructor
  · intro hP2 x hx
    refine ⟨interior (closure (interior A)), isOpen_interior, ?_, ?_⟩
    · exact hP2 hx
    · intro y hy
      exact hy
  · intro h
    intro x hx
    rcases h x hx with ⟨U, _hUopen, hxU, hUsubset⟩
    exact hUsubset hxU