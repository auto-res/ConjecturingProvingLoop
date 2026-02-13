

theorem P1_prod {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P1 A) (hB : P1 B) : P1 (A ×ˢ B) := by
  intro p hp
  -- Decompose the membership in the product set.
  rcases hp with ⟨hpA, hpB⟩
  -- Use `P1` on each coordinate.
  have hx : p.1 ∈ closure (interior A) := hA hpA
  have hy : p.2 ∈ closure (interior B) := hB hpB
  --------------------------------------------------------------------------------
  -- Step 1. `p` lies in the closure of `interior A ×ˢ interior B`.
  --------------------------------------------------------------------------------
  have h_mem :
      p ∈ closure ((interior A) ×ˢ (interior B) : Set (X × Y)) := by
    -- Rely on `closure_prod_eq`.
    have : p ∈ (closure (interior A) ×ˢ closure (interior B) : Set (X × Y)) :=
      ⟨hx, hy⟩
    simpa [closure_prod_eq] using this
  --------------------------------------------------------------------------------
  -- Step 2. Relate the two closures.
  --------------------------------------------------------------------------------
  have h_subset :
      closure ((interior A) ×ˢ (interior B) : Set (X × Y))
        ⊆ closure (interior (A ×ˢ B)) := by
    -- First show that `interior A ×ˢ interior B ⊆ interior (A ×ˢ B)`.
    have h_interior_subset :
        ((interior A) ×ˢ (interior B) : Set (X × Y))
          ⊆ interior (A ×ˢ B) := by
      -- It is an open subset of `A ×ˢ B`.
      have h_basic :
          ((interior A) ×ˢ (interior B) : Set (X × Y)) ⊆ (A ×ˢ B) := by
        intro q hq
        rcases hq with ⟨hqx, hqy⟩
        exact And.intro (interior_subset hqx) (interior_subset hqy)
      have h_open :
          IsOpen ((interior A) ×ˢ (interior B) : Set (X × Y)) :=
        isOpen_interior.prod isOpen_interior
      exact interior_maximal h_basic h_open
    -- Taking closures preserves inclusions.
    exact closure_mono h_interior_subset
  --------------------------------------------------------------------------------
  -- Step 3. Conclude.
  --------------------------------------------------------------------------------
  exact h_subset h_mem

theorem P3_prod {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P3 A) (hB : P3 B) : P3 (A ×ˢ B) := by
  intro p hp
  -- Decompose the membership in the product set.
  rcases hp with ⟨hpA, hpB⟩
  -- Apply `P3` on each coordinate.
  have hx : p.1 ∈ interior (closure (A : Set X)) := hA hpA
  have hy : p.2 ∈ interior (closure (B : Set Y)) := hB hpB
  -- Consider the open neighbourhood `U ×ˢ V` of `p`.
  let U : Set X := interior (closure (A : Set X))
  let V : Set Y := interior (closure (B : Set Y))
  have hU_open : IsOpen U := isOpen_interior
  have hV_open : IsOpen V := isOpen_interior
  have hUV_open : IsOpen (U ×ˢ V : Set (X × Y)) := hU_open.prod hV_open
  have hpUV : p ∈ (U ×ˢ V : Set (X × Y)) := by
    dsimp [U, V] at *
    exact And.intro hx hy
  -- Show that `U ×ˢ V ⊆ closure (A ×ˢ B)`.
  have h_subset_closure : (U ×ˢ V : Set (X × Y)) ⊆ closure (A ×ˢ B) := by
    intro q hq
    rcases hq with ⟨hqU, hqV⟩
    -- Points of `U` (resp. `V`) lie in `closure A` (resp. `closure B`).
    have hq1 : q.1 ∈ closure (A : Set X) := interior_subset hqU
    have hq2 : q.2 ∈ closure (B : Set Y) := interior_subset hqV
    have : (q : X × Y) ∈ (closure A ×ˢ closure B : Set (X × Y)) :=
      And.intro hq1 hq2
    -- Use `closure_prod_eq` to convert.
    simpa [closure_prod_eq] using this
  -- Hence `U ×ˢ V ⊆ interior (closure (A ×ˢ B))`.
  have h_subset_int :
      (U ×ˢ V : Set (X × Y)) ⊆ interior (closure (A ×ˢ B)) :=
    interior_maximal h_subset_closure hUV_open
  -- Conclude for `p`.
  exact h_subset_int hpUV