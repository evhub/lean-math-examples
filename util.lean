namespace util
    open function nat
    open classical (em prop_decidable)
    local attribute [instance] prop_decidable

    -- nat:
    @[simp] theorem le_zero_elim {n: nat}:
        n ≤ 0 ↔ n = 0 := begin
            apply iff.intro,
            apply eq_zero_of_le_zero,
            intro h0,
            rw [h0],
        end


    -- classical logic:
    @[simp] theorem not_not_elim (P: Prop):
        ¬¬P ↔ P := begin
            apply iff.intro,
            {
                intro hnn,
                by_contra hn,
                apply hnn,
                exact hn,
            },
            {
                intros h hn,
                apply hn,
                exact h,
            },
        end

    theorem not_forall_not_elim {T: Type _} {P: T → Prop} (hnfa: ¬ ∀ x: T, ¬ P x):
        ∃ x: T, P x := begin
            by_contra hnex,
            apply hnfa,
            intro x,
            by_contra hnP,
            apply hnex,
            apply exists.intro x hnP,
        end

    @[simp] theorem not_and (A B: Prop):
        ¬(A ∧ B) ↔ ¬A ∨ ¬B := begin
            apply iff.intro,
            {
                intro hAB,
                cases (em A);
                cases (em B),
                {
                    apply false.elim,
                    apply hAB,
                    split;
                    assumption,
                },
                {
                    right,
                    assumption,
                },
                all_goals {
                    left,
                    assumption,
                },
            },
            {
                intros hor hand,
                cases hor,
                case or.inl {
                    apply hor,
                    exact hand.1,
                },
                case or.inr {
                    apply hor,
                    exact hand.2,
                },
            },
        end


    -- isempty:
    @[reducible] def isempty (A: Sort _):
        Prop := ¬ nonempty A

    theorem isempty.elim {A: Sort _} (h: isempty A) (a: A):
        ∀ {P: Prop}, P := begin
            intros,
            apply false.elim,
            apply h,
            split,
            exact a,
        end


    -- function classes:
    attribute [class] injective
    attribute [class] surjective
    attribute [class] bijective

    instance bijective_of_inj_sur {T T': Sort _} {f: T → T'} [hfi: injective f] [hfs: surjective f]:
        bijective f := (| hfi, hfs |)

    instance inj_of_bijective {T T': Sort _} {f: T → T'} [hf: bijective f]:
        injective f := hf.1

    instance sur_of_bijective {T T': Sort _} {f: T → T'} [hf: bijective f]:
        surjective f := hf.2


    -- id:
    instance id.bijective {T: Sort _}:
        bijective (@id T) := begin
            split,
            show injective id, by {
                intros x y h,
                simp at h,
                exact h,
            },
            show surjective id, by {
                intro x,
                apply exists.intro x,
                simp,
            },
        end


    -- cast:
    @[simp] theorem cast_cast_elim {T T': Sort _} {x: T} (h: T = T') (h': T' = T):
        cast h' (cast h x) = x := begin
            cases h,
            refl,
        end

    theorem cast_eq_of_heq {T T': Sort _} {x: T} {x': T'}:
    x == x' →
    Σ' h: T = T',
    cast h x = x' := begin
        intro h,
        cases h,
        split,
        refl,
        refl,
    end

    theorem heq_of_cast_eq {T T': Sort _} {x: T} {x': T'} {h: T = T'}:
    cast h x = x' →
    x == x' := begin
        intro hcast,
        cases h,
        cases hcast,
        refl,
    end
end util
