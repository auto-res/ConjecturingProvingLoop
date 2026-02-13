

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : P1 A → P1 (e '' A) := by
  intro hP1
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` satisfies the `P1` condition
  have hx : x ∈ closure (interior (A : Set X)) := hP1 hxA
  ------------------------------------------------------------------
  -- 1.  `e x` lies in the closure of `e '' interior A`.
  ------------------------------------------------------------------
  have h1 : (e x : Y) ∈ closure (e '' interior (A : Set X)) := by
    have hmem : (e x : Y) ∈ e '' closure (interior (A : Set X)) :=
      ⟨x, hx, rfl⟩
    have h_eq :
        (e '' closure (interior (A : Set X))) =
          closure (e '' interior (A : Set X)) := by
      simpa using e.image_closure (interior (A : Set X))
    simpa [h_eq] using hmem
  ------------------------------------------------------------------
  -- 2.  `e '' interior A` is open and contained in `e '' A`, hence
  --     contained in `interior (e '' A)`.
  ------------------------------------------------------------------
  have hsubset :
      (e '' interior (A : Set X) : Set Y) ⊆
        interior (e '' (A : Set X)) := by
    -- openness
    have h_open : IsOpen (e '' interior (A : Set X)) := by
      -- express as a preimage under `e.symm`
      have h_eq :
          (e '' interior (A : Set X) : Set Y) =
            (fun y : Y => e.symm y) ⁻¹' interior (A : Set X) := by
        ext y
        constructor
        · intro hy
          rcases hy with ⟨u, hu, rfl⟩
          simp [hu]
        · intro hy
          exact ⟨e.symm y, hy, by simp⟩
      simpa [h_eq] using isOpen_interior.preimage e.symm.continuous
    -- inclusion into `e '' A`
    have h_incl : (e '' interior (A : Set X) : Set Y) ⊆ e '' (A : Set X) := by
      intro z hz
      rcases hz with ⟨u, huInt, rfl⟩
      exact ⟨u, interior_subset huInt, rfl⟩
    exact interior_maximal h_incl h_open
  ------------------------------------------------------------------
  -- 3.  Pass to closures and conclude.
  ------------------------------------------------------------------
  have h_closure :
      closure (e '' interior (A : Set X)) ⊆
        closure (interior (e '' (A : Set X))) :=
    closure_mono hsubset
  exact h_closure h1

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} : P2 B → P2 (e ⁻¹' B) := by
  intro hP2
  -- Transport `hP2` through the inverse homeomorphism `e.symm`
  have h1 : P2 (e.symm '' B) := by
    simpa using (P2_image_homeomorph e.symm) hP2
  -- Identify `e.symm '' B` with the preimage `e ⁻¹' B`
  have hEq : (e.symm '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      simpa using hyB
    · intro hx
      exact ⟨e x, hx, by simp⟩
  -- Rewrite using the above equality
  simpa [hEq] using h1

theorem P3_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} : P3 B → P3 (e ⁻¹' B) := by
  intro hP3
  -- Transport `P3` through the inverse homeomorphism `e.symm`
  have h1 : P3 (e.symm '' B) := by
    simpa using (P3_image_homeomorph e.symm) hP3
  -- Identify the image with the preimage
  have hEq : (e.symm '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      simpa using hyB
    · intro hx
      exact ⟨e x, hx, by simp⟩
  -- Prove the required `P3` statement
  intro x hx
  have hx' : x ∈ (e.symm '' B : Set X) := by
    simpa [hEq] using hx
  have hxInt : x ∈ interior (closure (e.symm '' B : Set X)) := h1 hx'
  simpa [hEq] using hxInt

theorem P1_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P1 A := by
  intro x hx
  -- First, show that `A = univ` since `A` is nonempty and the space is a subsingleton.
  have hAuniv : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _;
      -- Any element `y` equals `x`, hence belongs to `A`.
      have h_eq : y = x := Subsingleton.elim y x
      simpa [h_eq] using hx
  -- Re-express the goal using this equality and finish by `simp`.
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [hAuniv, interior_univ, closure_univ] using this