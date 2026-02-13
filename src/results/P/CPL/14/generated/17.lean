

theorem P1_closure {X} [TopologicalSpace X] {A : Set X} : P1 A → P1 (closure A) := by
  intro hP1
  intro x hx
  -- First inclusion: `closure A ⊆ closure (interior A)`
  have h1 : (closure (A : Set X)) ⊆ closure (interior A) := by
    have h : (A : Set X) ⊆ closure (interior A) := hP1
    simpa [closure_closure] using closure_mono h
  -- Second inclusion: `closure (interior A) ⊆ closure (interior (closure A))`
  have h2 : closure (interior A) ⊆ closure (interior (closure A)) := by
    have h : (interior A : Set X) ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono h
  -- Combine the inclusions
  have hsubset : (closure (A : Set X)) ⊆ closure (interior (closure A)) :=
    h1.trans h2
  exact hsubset hx

theorem P2_interior_uncond {X} [TopologicalSpace X] {A : Set X} : P2 (interior A) := by
  intro x hx
  -- `interior A` is open and contained in its closure, hence in the interior of that closure.
  have hsubset : (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal subset_closure isOpen_interior
  -- Apply the inclusion and simplify.
  simpa [interior_interior] using hsubset hx

theorem P3_singleton_of_dense {X} [TopologicalSpace X] {x : X} : Dense ({x} : Set X) → P3 ({x} : Set X) := by
  intro hDense
  have hclosure : closure ({x} : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  exact P3_of_dense (A := ({x} : Set X)) hclosure

theorem P2_prod {X Y} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 A → P2 B → P2 (A ×ˢ B) := by
  intro hA hB
  intro p hp
  -- Split the hypothesis on the product set.
  rcases hp with ⟨hAp, hBp⟩
  -- Auxiliary open neighbourhoods coming from the `P2` hypotheses.
  let U : Set X := interior (closure (interior A))
  let V : Set Y := interior (closure (interior B))
  have hxU : p.1 ∈ U := by
    dsimp [U] at *
    exact hA hAp
  have hyV : p.2 ∈ V := by
    dsimp [V] at *
    exact hB hBp
  have h_mem : p ∈ U ×ˢ V := by
    exact ⟨hxU, hyV⟩
  -- `U ×ˢ V` is open.
  have h_open : IsOpen (U ×ˢ V) := by
    have hUopen : IsOpen U := by
      dsimp [U]; exact isOpen_interior
    have hVopen : IsOpen V := by
      dsimp [V]; exact isOpen_interior
    exact hUopen.prod hVopen
  ----------------------------------------------------------------
  -- 1.  `U ×ˢ V ⊆ closure (interior A) ×ˢ closure (interior B)`.
  ----------------------------------------------------------------
  have h_sub₁ :
      (U ×ˢ V) ⊆ closure (interior A) ×ˢ closure (interior B) := by
    intro q hq
    rcases hq with ⟨hq1, hq2⟩
    dsimp [U, V] at hq1 hq2
    exact ⟨interior_subset hq1, interior_subset hq2⟩
  ----------------------------------------------------------------
  -- 2.  `closure (interior A) ×ˢ closure (interior B)`
  --     ⊆ `closure (interior (A ×ˢ B))`.
  ----------------------------------------------------------------
  -- First, `interior A × interior B` is an open subset of `A × B`,
  -- hence it lies in the interior of `A × B`.
  have h_int_prod_subset :
      interior A ×ˢ interior B ⊆ interior (A ×ˢ B) := by
    have h_into : interior A ×ˢ interior B ⊆ A ×ˢ B := by
      intro q hq; exact ⟨interior_subset hq.1, interior_subset hq.2⟩
    have h_open_int : IsOpen (interior A ×ˢ interior B) :=
      (isOpen_interior).prod isOpen_interior
    exact interior_maximal h_into h_open_int
  -- Taking closures gives the next inclusion.
  have h_closure_subset :
      closure (interior A ×ˢ interior B) ⊆
        closure (interior (A ×ˢ B)) :=
    closure_mono h_int_prod_subset
  -- Identify the left–hand side using `closure_prod_eq`.
  have h_prod_closure_eq :
      closure (interior A ×ˢ interior B) =
        closure (interior A) ×ˢ closure (interior B) := by
    simpa using
      (closure_prod_eq (s := interior A) (t := interior B))
  have h_sub₂ :
      closure (interior A) ×ˢ closure (interior B) ⊆
        closure (interior (A ×ˢ B)) := by
    simpa [h_prod_closure_eq] using h_closure_subset
  ----------------------------------------------------------------
  -- 3.  Combine the two inclusions.
  ----------------------------------------------------------------
  have h_sub_total :
      (U ×ˢ V) ⊆ closure (interior (A ×ˢ B)) :=
    Set.Subset.trans h_sub₁ h_sub₂
  ----------------------------------------------------------------
  -- 4.  Pass to the interior of the target set.
  ----------------------------------------------------------------
  have h_sub_int :
      (U ×ˢ V) ⊆ interior (closure (interior (A ×ˢ B))) :=
    interior_maximal h_sub_total h_open
  ----------------------------------------------------------------
  -- 5.  Conclude the desired membership.
  ----------------------------------------------------------------
  exact h_sub_int h_mem

theorem P3_prod {X Y} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P3 A → P3 B → P3 (A ×ˢ B) := by
  intro hA hB
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- Open neighbourhood for the first component
  obtain ⟨U, hUopen, hp1U, hUsubset⟩ :=
    (P3_iff_forall_point).1 hA _ hpA
  -- Open neighbourhood for the second component
  obtain ⟨V, hVopen, hp2V, hVsubset⟩ :=
    (P3_iff_forall_point).1 hB _ hpB
  -- The product of the two neighbourhoods is open
  have h_open : IsOpen (U ×ˢ V) := hUopen.prod hVopen
  -- The point `p` lies in this product neighbourhood
  have hp_in : p ∈ U ×ˢ V := by
    exact ⟨hp1U, hp2V⟩
  -- The product neighbourhood is contained in the closure of `A ×ˢ B`
  have hsubset_closure : (U ×ˢ V) ⊆ closure (A ×ˢ B) := by
    intro q hq
    rcases hq with ⟨hqU, hqV⟩
    have hmem : q ∈ closure A ×ˢ closure B := ⟨hUsubset hqU, hVsubset hqV⟩
    simpa [closure_prod_eq] using hmem
  -- Hence it is contained in the interior of that closure
  have hsubset_int :
      (U ×ˢ V) ⊆ interior (closure (A ×ˢ B)) :=
    interior_maximal hsubset_closure h_open
  -- Conclude the desired membership
  exact hsubset_int hp_in