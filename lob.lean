import .lawvere

namespace lob
    open function

    open util lawvere

    -- diagonal lemma:
    def S0: Type := Prop

    def S1: Type := S0 → S0

    def up (ψ: S0): S1 :=
        const S0 ψ

    theorem diag {f: S1 → S1 → S0} (sur_f: surjective f):
        ∀ φ: S1,
        ∃ ψ: S0,
        ψ = f φ (up ψ) :=
            assume φ: S1,
            let h: S0 → S0 := f φ ∘ up in
            simple_lawvere.{0 0} sur_f h


    -- lob axioms:
    constant Bew: S0 → S0

    constant godnum: S1 → S0

    def box: S0 → S0 := Bew ∘ godnum ∘ up

    def proves: S0 → Prop := box

    namespace hilbert_bernay
        axiom a:
            ∀ {φ: S0},
            proves φ → proves (box φ)

        axiom b:
            ∀ {φ: S0},
            proves (box φ → box (box φ))

        axiom c:
            ∀ {φ ψ: S0},
            proves (box (φ → ψ) → box φ → box ψ)
    end hilbert_bernay

    def f (φ: S1) (ψ: S1): S0 :=
        φ (godnum ψ)

    axiom sur_f: surjective f

    axiom proves.mp:
        ∀ {φ ψ: S0},
        proves (φ → ψ) → proves φ → proves ψ

    axiom proves.implies_trans:
        ∀ {a b c: S0},
        proves (a → b) → proves (b → c) → proves (a → c)

    axiom proves.implies_middleman_elim:
        ∀ {a b c: S0},
        proves (a → b → c) → proves (a → b) → proves (a → c)

    axiom proves.diag:
        ∀ φ: S1,
        ∃ ψ: S0,
        proves (ψ ↔ f φ (up ψ))

    axiom proves.iff_mp:
        ∀ {a b: S0},
        proves (a ↔ b) → proves (a → b)

    axiom proves.iff_mpr:
        ∀ {a b: S0},
        proves (a ↔ b) → proves (b → a)


    -- lob's theorem:
    def h (ψ: S0) (x: S0): S0 :=
        Bew x → ψ

    @[simp] theorem f_of_h:
        ∀ {ψ φ: S0},
        f (h ψ) (up φ) = (box φ → ψ) :=
            assume ψ φ: S0,
            rfl

    theorem lob {ψ: S0} (h0: proves (box ψ → ψ)): proves ψ :=
        exists.elim (proves.diag (h ψ)) (
            assume φ: S0,
            assume heq: proves (φ ↔ f (h ψ) (up φ)),
            have h1: proves (φ ↔ (box φ → ψ)),
                by {simp at heq, exact heq},
            have h1_forward: proves (φ → (box φ → ψ)),
                from h1.iff_mp,
            have h1_reverse: proves ((box φ → ψ) → φ),
                from h1.iff_mpr,
            have h2: proves (box (φ → (box φ → ψ))),
                from hilbert_bernay.a h1_forward,
            have h3: proves (box φ → box (box φ → ψ)),
                from hilbert_bernay.c.mp h2,
            have h4: proves (box φ → box (box φ) → box ψ),
                from h3.implies_trans hilbert_bernay.c,
            have h5: proves (box φ → box (box φ)),
                from hilbert_bernay.b,
            have h6: proves (box φ → box ψ),
                from h4.implies_middleman_elim h5,
            have h7: proves (box φ → ψ),
                from h6.implies_trans h0,
            have h8: proves φ,
                from h1_reverse.mp h7,
            have h9: proves (box φ),
                from hilbert_bernay.a h8,
            show proves ψ,
                from h7.mp h9
        )


    -- godel's second incompleteness theorem:
    theorem godel: proves (¬box false) → proves false := lob
end lob
