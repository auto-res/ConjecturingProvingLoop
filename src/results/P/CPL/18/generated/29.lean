

theorem P3_union_sInter {X : Type*} [TopologicalSpace X] {A : Set (Set X)} (hA : ∀ B ∈ A, Topology.P3 B) : Topology.P3 (Set.sUnion A ∪ Set.sInter A) := by
  classical
  rcases (Set.eq_empty_or_nonempty (A : Set (Set X))) with hAempty | hAnonempty
  · -- Case `A = ∅`
    -- Then `⋃₀ A = ∅` and `⋂₀ A = univ`, so the union is `univ`,
    -- which satisfies `P3`.
    have : Topology.P3 (Set.univ : Set X) := P3_univ (X := X)
    simpa [hAempty] using this
  · -- Case `A` is non‐empty
    rcases hAnonempty with ⟨B₀, hB₀⟩
    -- `⋂₀ A ⊆ ⋃₀ A`
    have hsubset : (Set.sInter A : Set X) ⊆ Set.sUnion A := by
      intro x hx
      have hxB₀ : x ∈ B₀ := (Set.mem_sInter.1 hx) _ hB₀
      exact Set.mem_sUnion.2 ⟨B₀, hB₀, hxB₀⟩
    -- Hence the union is just `⋃₀ A`.
    have h_union_eq :
        (Set.sUnion A ∪ Set.sInter A : Set X) = Set.sUnion A :=
      Set.union_eq_self_of_subset_right hsubset
    -- Apply `P3` to `⋃₀ A`.
    have hP3 : Topology.P3 (Set.sUnion A) :=
      P3_sUnion (X := X) (𝒜 := A) hA
    simpa [h_union_eq] using hP3

theorem P2_iterate {X : Type*} [TopologicalSpace X] {A : ℕ → Set X} (h0 : Topology.P2 (A 0)) (hstep : ∀ n, Topology.P2 (A n) → Topology.P2 (A (n+1))) : ∀ n, Topology.P2 (A n) := by
  intro n
  induction n with
  | zero =>
      simpa using h0
  | succ n ih =>
      exact hstep n ih

theorem P1_eq_of_subset {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) (hBA : B ⊆ closure (interior A)) : Topology.P1 A → Topology.P1 B := by
  intro _hPA
  dsimp [Topology.P1] at _hPA ⊢
  intro x hxB
  -- From `hBA` we have that `x` lies in `closure (interior A)`.
  have hx_clA : x ∈ closure (interior (A : Set X)) := hBA hxB
  -- Since `A ⊆ B`, we get `interior A ⊆ interior B`.
  have h_interior : (interior (A : Set X)) ⊆ interior B :=
    interior_mono hAB
  -- Taking closures yields the desired inclusion.
  have h_closure : closure (interior (A : Set X)) ⊆ closure (interior B) :=
    closure_mono h_interior
  -- Conclude that `x ∈ closure (interior B)`.
  exact h_closure hx_clA