

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P1 A) (hB : P1 B) : P1 (A ×ˢ B) := by
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- Each coordinate belongs to the corresponding closure.
  have hx : p.1 ∈ closure (interior A) := hA hpA
  have hy : p.2 ∈ closure (interior B) := hB hpB
  -- Hence `p` is in the product of these closures, which equals the closure
  -- of the product of the interiors.
  have h_mem_closure_prod : p ∈ closure ((interior A) ×ˢ (interior B)) := by
    have : p ∈ (closure (interior A) ×ˢ closure (interior B)) := by
      exact ⟨hx, hy⟩
    simpa [closure_prod_eq] using this
  -- The product of the interiors sits inside the interior of `A ×ˢ B`.
  have h_subset :
      ((interior A) ×ˢ (interior B) : Set (X × Y)) ⊆ interior (A ×ˢ B) := by
    -- First, it is contained in `A ×ˢ B`.
    have h_incl :
        ((interior A) ×ˢ (interior B) : Set (X × Y)) ⊆ (A ×ˢ B) := by
      intro z hz
      rcases hz with ⟨hzA, hzB⟩
      exact ⟨interior_subset hzA, interior_subset hzB⟩
    -- It is an open set.
    have h_open :
        IsOpen ((interior A) ×ˢ (interior B) : Set (X × Y)) :=
      (isOpen_interior.prod isOpen_interior)
    -- Therefore it is contained in the interior of `A ×ˢ B`.
    exact interior_maximal h_incl h_open
  -- Taking closures preserves inclusion.
  have h_closure_subset :
      closure ((interior A) ×ˢ (interior B)) ⊆
        closure (interior (A ×ˢ B)) :=
    closure_mono h_subset
  exact h_closure_subset h_mem_closure_prod

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P2 A) (hB : P2 B) : P2 (A ×ˢ B) := by
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- Apply `P2` to each coordinate.
  have hx : p.1 ∈ interior (closure (interior A)) := hA hpA
  have hy : p.2 ∈ interior (closure (interior B)) := hB hpB
  -- The point `p` lies in the following open rectangle.
  have h_mem :
      p ∈
        ((interior (closure (interior A))) ×ˢ
          (interior (closure (interior B)))) := by
    exact ⟨hx, hy⟩
  -- This rectangle is open.
  have h_open :
      IsOpen
        ((interior (closure (interior A))) ×ˢ
          (interior (closure (interior B))) : Set (X × Y)) :=
    (isOpen_interior.prod isOpen_interior)
  -- Show the rectangle is contained in the closure of
  -- `(interior A) ×ˢ (interior B)`.
  have h_sub :
      ((interior (closure (interior A))) ×ˢ
        (interior (closure (interior B))) : Set (X × Y)) ⊆
        closure ((interior A) ×ˢ (interior B)) := by
    intro z hz
    rcases hz with ⟨hz1, hz2⟩
    have hz1_cl : z.1 ∈ closure (interior A) :=
      (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hz1
    have hz2_cl : z.2 ∈ closure (interior B) :=
      (interior_subset : interior (closure (interior B)) ⊆ closure (interior B)) hz2
    have : (z : X × Y) ∈ (closure (interior A) ×ˢ closure (interior B)) :=
      ⟨hz1_cl, hz2_cl⟩
    simpa [closure_prod_eq] using this
  -- Hence the rectangle sits inside the desired interior.
  have h_sub_int :
      ((interior (closure (interior A))) ×ˢ
        (interior (closure (interior B))) : Set (X × Y)) ⊆
        interior (closure ((interior A) ×ˢ (interior B))) :=
    interior_maximal h_sub h_open
  -- Conclude for the given point `p`.
  have h_final :
      p ∈ interior (closure ((interior A) ×ˢ (interior B))) :=
    h_sub_int h_mem
  -- Rewrite using `interior_prod_eq` to match the goal.
  simpa [interior_prod_eq] using h_final

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P3 A) (hB : P3 B) : P3 (A ×ˢ B) := by
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- Each coordinate lies in the interior of the corresponding closure.
  have hA_int : p.1 ∈ interior (closure (A : Set X)) := hA hpA
  have hB_int : p.2 ∈ interior (closure (B : Set Y)) := hB hpB
  -- Hence `p` lies in the following open rectangle.
  have h_mem :
      p ∈
        ((interior (closure (A : Set X))) ×ˢ
          (interior (closure (B : Set Y)))) := by
    exact ⟨hA_int, hB_int⟩
  -- This rectangle is open.
  have h_open :
      IsOpen
        ((interior (closure (A : Set X))) ×ˢ
          (interior (closure (B : Set Y))) : Set (X × Y)) :=
    (isOpen_interior.prod isOpen_interior)
  -- Show the rectangle is contained in the closure of `A ×ˢ B`.
  have h_incl :
      ((interior (closure (A : Set X))) ×ˢ
          (interior (closure (B : Set Y))) : Set (X × Y)) ⊆
        closure (A ×ˢ B) := by
    intro z hz
    rcases hz with ⟨hzA, hzB⟩
    have hzA_cl : (z.1 : X) ∈ closure (A : Set X) :=
      (interior_subset :
        interior (closure (A : Set X)) ⊆ closure A) hzA
    have hzB_cl : (z.2 : Y) ∈ closure (B : Set Y) :=
      (interior_subset :
        interior (closure (B : Set Y)) ⊆ closure B) hzB
    have : (z : X × Y) ∈ (closure (A : Set X)) ×ˢ (closure (B : Set Y)) :=
      ⟨hzA_cl, hzB_cl⟩
    simpa [closure_prod_eq] using this
  -- Therefore the rectangle sits inside the desired interior.
  have h_sub_int :
      ((interior (closure (A : Set X))) ×ˢ
          (interior (closure (B : Set Y))) : Set (X × Y)) ⊆
        interior (closure (A ×ˢ B)) :=
    interior_maximal h_incl h_open
  exact h_sub_int h_mem