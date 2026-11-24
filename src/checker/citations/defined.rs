//! Defined functions and the domains asked of them.

use std::slice;

use super::*;
use crate::checker::record::{AppliedDomain, DomainSaid, Substituted};
use crate::corpus::{proof, DefineLine};
use crate::methods::membership;
use crate::notations::TENDS_TO;
use crate::{citing, matching, sorts, Checked};

/// A defined function by name, with the domain of each argument in order.
#[derive(Clone)]
pub(in crate::checker) struct Defined {
    pub(super) name: String,
    /// The label a line cites it by; None for an import that gives none.
    pub(super) label: Option<String>,
    /// Each argument's domain, as the define writes it.
    pub(super) domains: Vec<Written>,
    /// Defined by recursion, whose domain is its step clause's index: the
    /// clause at k + 1 holds for k in the domain, and the base clause for
    /// its one argument.
    pub(super) recursive: bool,
}

/// A cited item's `let f : D → E` asks nothing of a function the citing
/// proof introduces with a type, `let g : X → Y`, whose type is its sort,
/// as a letter's membership is (`READERS.md`, a function's type). Of any
/// other f it asks a fact, which the step names, in its `from` or by a
/// requires line (R1): a function the proof defines has no type until a
/// line says one, `G : [a, b] → ℝ` by `function-into`.
pub fn check_defined_types(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
    scopes: &[FileScope],
) {
    let defines = proof::in_scope(thm, scopes);
    let mut defined: IndexMap<String, Option<DefinedRule>> =
        defined_functions(&defines)
            .into_iter()
            .map(|d| (d.name, None))
            .collect();
    // Each rule read in this theorem's file: an imported define is read in
    // the file that writes it, and its rule is not this file's to read.
    for d in defines.iter().filter(|d| !d.imported) {
        // A define that does not read is said where it is written, by
        // `check_formulas` of a theorem's and `check_file_defines` of a
        // file's.
        if let Ok(Some(rule)) = DefinedRule::of(d.define, known) {
            defined.insert(rule.name.clone(), Some(rule));
        }
    }
    for step in &thm.steps {
        let letters = super::super::library::introduced(known, step);
        let at = DefinedAt {
            defined: &defined,
            letters: &letters,
        };
        if let Some(item) = step.just.cited_item() {
            let name = step.just.item(&item);
            let parts = known.read_out_parts(step, library);
            for said in defined_types_unsaid(&parts, &name, &at, library, known) {
                report.say(
                    &thm.path,
                    step.just.line,
                    format!(
                        "step {} cites {item}, which asks for {}, and nothing it cites or requires says it; a requires line says it, as {}, from a line saying the values on a set holding {}",
                        step.number,
                        known.print(&said),
                        values_everywhere(&said, known),
                        said.children.get(1).map(|d| known.print(d)).unwrap_or_default()
                    ),
                );
            }
        }
        for req in &step.requires {
            let Some((item, _)) = req.cited_item() else {
                continue;
            };
            let name = step.just.item(&item);
            let Some(parts) =
                requires_parts(step, req, &[], known, library, Spelt::ReadOut)
            else {
                continue;
            };
            for said in defined_types_unsaid(&parts, &name, &at, library, known) {
                report.say(
                    &thm.path,
                    req.line,
                    format!(
                        "the requires line of {} cites {item}, which asks for {}, and nothing it cites says it",
                        step.called(),
                        known.print(&said)
                    ),
                );
            }
        }
    }
}

/// A function a define gives of one argument, read: `t(j) = j + 1, for j ∈
/// ℕ` is t with letter j, domain ℕ and rule j + 1.
pub(super) struct DefinedRule {
    pub(super) name: String,
    pub(super) letter: String,
    pub(super) domain: Node,
    pub(super) rule: Node,
}

impl DefinedRule {
    /// The define's function of one argument, read with its argument's
    /// sort; None for a define of anything else. A part that does not read
    /// is a defect.
    pub(super) fn of(d: &DefineLine, known: &Known) -> Checked<Option<DefinedRule>> {
        let Built(DefineParts::One(one)) = define_parts(&d.text) else {
            return Ok(None);
        };
        let [param] = one.params.as_slice() else {
            return Ok(None);
        };
        let local =
            sorts::define_sorts(&one, &known.sorts, known.env.g, &d.path, d.line)?;
        let rule = d.rule(&one.body).formula()?.read(known.env.g, &local)?;
        let domain = known.parse(&d.domain(param).formula()?)?;
        Ok(Some(DefinedRule {
            name: one.name.clone(),
            letter: param.name.clone(),
            domain,
            rule,
        }))
    }

    /// Whether the type `f : D → E` asked of this function is said once
    /// (`SYNTAX.md`, "A define with a parameter also states what its
    /// function is on"): its domain holds D, and its rule at a point of D
    /// by what the page says once, with `letters` the step's, puts its
    /// values in E.
    pub(super) fn typed_once(
        &self,
        domain: &Node,
        codomain: &Node,
        letters: &Introduced,
        known: &Known,
    ) -> bool {
        let Some(into) = (codomain.notation() == NUMBER_SYSTEMS)
            .then(|| System::of_sign(&codomain.text))
            .flatten()
        else {
            return false;
        };
        let inside = match domain.notation() {
            INTEGER_RANGE => range_system(domain),
            NUMBER_SYSTEMS => System::of_sign(&domain.text),
            _ => None,
        };
        let holds = known.alike(&self.domain, domain)
            || (self.domain.notation() == NUMBER_SYSTEMS
                && System::of_sign(&self.domain.text)
                    .zip(inside)
                    .is_some_and(|(own, asked)| asked.within(own)));
        let Some(inside) = inside.filter(|_| holds) else {
            return false;
        };
        let mut letters = letters.clone();
        letters.insert(self.letter.clone(), inside);
        // The rule's value at its own parameter: a line speaks of the
        // proof's letters, not of it, so the one rule reads no line
        // (`membership::shown`).
        let given = membership::Facts {
            facts: &[],
            letters,
            ranged: IndexMap::new(),
            typed: &[],
            in_sums: &[],
            targets: known.targets,
            ctx: known.ctx,
        };
        membership::holds(&self.rule, into, &given)
    }
}

/// The functions the theorem and its file define, each with its rule where
/// it is of one argument, and the letters the page says once at a step.
pub(super) struct DefinedAt<'a> {
    pub(super) defined: &'a IndexMap<String, Option<DefinedRule>>,
    pub(super) letters: &'a Introduced,
}

/// Of each step citing a function a define lets on a domain, or
/// substituting the define's equation, what says the argument it applies
/// the function at is in that domain (`CheckedTheorem::define_domains`).
/// A step citing the define applies it in its claim, a substitute in its
/// equation (`substituted`). The membership is found, in this order: among
/// the step's facts, placed in a line it cites (`formulas::fact_placed`);
/// in the claim's own "for all", whose member is the argument and whose set
/// lies inside the domain; on the `let` line introducing the argument. By
/// the step's line; a step where none says it is left out.
pub fn define_domains(
    thm: &Theorem,
    library: &Library,
    known: &Known,
    substituted: &IndexMap<usize, Substituted>,
) -> IndexMap<usize, Vec<AppliedDomain>> {
    let mut out = IndexMap::new();
    for step in &thm.steps {
        let Some(claim) = known.whole_as_written(&step.claim) else {
            continue;
        };
        let (label, applied) = match (&step.just.head, step.just.source.as_ref()) {
            (Head::Define, _) => match step.just.defined.as_deref() {
                Some(label) => (label, claim.clone()),
                None => continue,
            },
            (_, Some(Source::At(place))) => match substituted.get(&step.just.line) {
                Some(rec) => (place.named(), rec.equation.clone()),
                None => continue,
            },
            _ => continue,
        };
        let Some(d) = thm.defines.iter().find(|d| d.label == label) else {
            continue;
        };
        let Ok(Some(rule)) = DefinedRule::of(d, known) else {
            continue;
        };
        let parts = known.read_out_parts(step, library);
        let said_of = |arg: &Node| -> Option<DomainSaid> {
            let cited = parts.facts.iter().find(|fact| {
                fact.notation() == MEMBERSHIP
                    && fact.children.len() == 2
                    && known.alike(&fact.children[0], arg)
                    && known.alike(&fact.children[1], &rule.domain)
            });
            if let Some(at) = cited
                .and_then(|fact| super::super::formulas::fact_placed(step, fact, known))
            {
                return Some(DomainSaid::Line(at));
            }
            if member_in_domain(&claim, arg, &rule.domain, known) {
                return Some(DomainSaid::Member);
            }
            let fact =
                page::made(library.env.g, IN, vec![arg.clone(), rule.domain.clone()]);
            introduced_placed(thm, step, &fact, known).map(DomainSaid::Line)
        };
        let found: Vec<AppliedDomain> = applied
            .walk()
            .into_iter()
            .filter_map(|n| {
                let [f, arg] = n.children.as_slice() else {
                    return None;
                };
                if n.notation() != APPLICATION || !f.is_name() || f.text != rule.name {
                    return None;
                }
                Some(AppliedDomain {
                    label: label.to_string(),
                    arg: arg.clone(),
                    said: said_of(arg)?,
                })
            })
            .collect();
        if !found.is_empty() {
            out.insert(step.just.line, found);
        }
    }
    out
}

/// Of each step of a method or an item citing a function its theorem lets
/// on a domain, each application the step asks the domain of, and what says
/// the argument is in it (`CheckedTheorem::applied_domains`): `q(a)` of H4
/// in a transitivity from H4, D1, H5, and `a ∈ ℕ` on the `let` line; V(N) of
/// a claim `{N} ∈ V(N)` citing an item from D1, and `N ∈ {1, …, N}` of H2. The
/// applications are those `evaluated` finds; each membership is found as
/// `define_domains` finds one. A step whose define, substitution or
/// calculation puts the equation in itself (`define_domains`), or whose
/// membership Lean's types give, is not one; nor is an application none
/// says the domain of, which `check_define_domains` reports.
pub fn applied_domains(
    thm: &Theorem,
    library: &Library,
    known: &Known,
    scopes: &[FileScope],
) -> IndexMap<usize, Vec<AppliedDomain>> {
    let functions = defined_functions(&proof::in_scope(thm, scopes));
    let mut out = IndexMap::new();
    for step in &thm.steps {
        let asks = matches!(&step.just.head, Head::Method(_) | Head::Item { .. });
        if !asks {
            continue;
        }
        let used: Vec<Defined> = functions
            .iter()
            .filter(|f| f.label.as_ref().is_some_and(|l| step.just.refs.contains(l)))
            .cloned()
            .collect();
        if used.is_empty() {
            continue;
        }
        let Some(claim) = known.whole_as_written(&step.claim) else {
            continue;
        };
        let parts = known.read_out_parts(step, library);
        let letters = super::super::library::introduced(known, step);
        // An argument that is the index of a sum or a sequence's limit in
        // `formula` whose range lies inside the domain.
        let index_said = |formula: &Node, arg: &Node, domain: &Node| {
            let formulas = slice::from_ref(formula);
            let within = index_range_within(
                formulas,
                arg,
                domain,
                &letters,
                known,
                &library.ctx,
            );
            (within == Some(true)).then(|| match limit_index(formulas, arg) {
                true => DomainSaid::LimitIndex,
                false => DomainSaid::SumRange,
            })
        };
        let mut found = Vec::new();
        for asked in evaluated(step, &used, known, library) {
            let Some(fact) = asked.says.first() else {
                continue;
            };
            let [_, domain] = fact.children.as_slice() else {
                continue;
            };
            let cited = parts.facts.iter().find(|f| known.alike(f, fact));
            let said = cited
                .and_then(|f| super::super::formulas::fact_placed(step, f, known))
                .map(DomainSaid::Line)
                .or_else(|| {
                    member_in_domain(&claim, &asked.arg, domain, known)
                        .then_some(DomainSaid::Member)
                })
                .or_else(|| {
                    introduced_placed(thm, step, fact, known).map(DomainSaid::Line)
                })
                .or_else(|| index_said(&claim, &asked.arg, domain));
            if let Some(said) = said {
                found.push(AppliedDomain {
                    label: asked.label.clone(),
                    arg: asked.arg.clone(),
                    said,
                });
            }
        }
        // An application in a line the step cites at a letter the line binds,
        // S(n) of `S(n) → K as n → ∞`.
        for (asked, part) in applied_at_bound_in_cited(step, &used, known, &library.ctx)
        {
            let Some(domain) = asked.says.first().and_then(|f| f.children.get(1))
            else {
                continue;
            };
            if let Some(said) = index_said(&part, &asked.arg, domain) {
                found.push(AppliedDomain {
                    label: asked.label.clone(),
                    arg: asked.arg.clone(),
                    said,
                });
            }
        }
        if !found.is_empty() {
            out.insert(step.just.line, found);
        }
    }
    out
}

/// Whether `claim` is said of every member of a set inside `domain`, and
/// `arg` is that member: the set is the domain, or a range whose number
/// system it is (`range_system`).
pub(super) fn member_in_domain(
    claim: &Node,
    arg: &Node,
    domain: &Node,
    known: &Known,
) -> bool {
    let (FOR_ALL, [letter, set, _]) = (claim.notation(), claim.children.as_slice())
    else {
        return false;
    };
    if !letter.is_name() || !arg.is_name() || letter.text != arg.text {
        return false;
    }
    let inside = match set.notation() {
        INTEGER_RANGE => range_system(set),
        _ => None,
    };
    known.alike(set, domain)
        || (domain.notation() == NUMBER_SYSTEMS
            && inside.is_some()
            && inside == System::of_sign(&domain.text))
}

/// The `let` line in scope at `step` that says `fact`, placed in it, as
/// `formulas::fact_placed` places a cited line's: the line that introduces
/// a define's argument, where no line the step cites says it is in the
/// domain.
pub(super) fn introduced_placed(
    thm: &Theorem,
    step: &Step,
    fact: &Node,
    known: &Known,
) -> Option<FirstAt> {
    let scope = known.scope(step);
    let defined = known.citing_step(step);
    let lets = thm
        .hypotheses
        .iter()
        .filter(|h| h.kind == Intro::Let)
        .filter_map(|h| h.label.clone())
        .chain(
            thm.steps
                .iter()
                .flat_map(|s| &s.openers)
                .filter(|o| o.kind == Intro::Let)
                .map(|o| o.label.clone()),
        );
    lets.into_iter().find_map(|r| {
        let stated = scope.get(r.as_str())?;
        let says = known.says(stated, &defined);
        let s = says.iter().find(|s| known.alike(&s.cited, fact))?;
        placed(&r, s, &says, known.sentence_count(stated))
    })
}

/// Each type the item named asks of a function `at` defines
/// (`check_defined_types`), at what its letters stand for, that no fact of
/// `parts` says and that is not said once of its rule.
pub(super) fn defined_types_unsaid(
    parts: &Parts,
    name: &str,
    at: &DefinedAt,
    library: &Library,
    known: &Known,
) -> Vec<Node> {
    let typed = library.function_types(name);
    if typed.is_empty() {
        return Vec::new();
    }
    let stands = stood_for(parts, name, library);
    let mut out = Vec::new();
    for t in &typed {
        let Some(v) = t.children.first().and_then(|f| stands.get(&f.text)) else {
            continue;
        };
        if !v.is_name() {
            continue;
        }
        let Some(rule) = at.defined.get(v.text.as_str()) else {
            continue;
        };
        let typed = substitute_apart(t, &stands, &library.ctx);
        let said = parts.facts.iter().any(|fact| {
            TYPING.contains(&fact.notation())
                && fact.children.first().is_some_and(|g| g.text == v.text)
        });
        let once = rule.as_ref().is_some_and(|r| {
            r.typed_once(&typed.children[1], &typed.children[2], at.letters, known)
        });
        if !said && !once && !values_said(&typed, &parts.facts, library) {
            out.push(typed);
        }
    }
    out
}

/// A function's type `f : D → E` said of its values, `for all k ∈ D, f(k)
/// ∈ E`, as a message writes it (`values_said`).
pub(super) fn values_everywhere(typed: &Node, known: &Known) -> String {
    match typed.children.as_slice() {
        [f, domain, codomain] => format!(
            "for all k ∈ {}, {}(k) ∈ {}",
            known.print(domain),
            known.print(f),
            known.print(codomain)
        ),
        _ => known.print(typed),
    }
}

/// Whether a fact says a function's type `f : D → E` of its values, `for
/// all k ∈ D, f(k) ∈ E`, as a step citing a sum's item over a range writes
/// it of a defined function (`tests/elaborator/a-for-all-over-a-range`).
pub(super) fn values_said(typed: &Node, facts: &[Node], library: &Library) -> bool {
    let [f, domain, codomain] = typed.children.as_slice() else {
        return false;
    };
    let g = library.env.g;
    let k = Node::name(domain.sort.held().unwrap_or_else(Sort::none), "k");
    let Some(value) = page::made_as(g, "_(_)", vec![f.clone(), k.clone()]) else {
        return false;
    };
    let member = bound_in(Bound::Member, &value, codomain, library.env.g);
    let Some(every) =
        page::made_as(g, "for all _ ∈ _, _", vec![k, domain.clone(), member])
    else {
        return false;
    };
    let none = IndexMap::new();
    facts
        .iter()
        .any(|fact| matching::alike(fact, &every, &library.ctx, &none, &none))
}

/// The functions the defines a theorem may use name (`corpus::in_scope`),
/// each under the name and label the theorem uses.
pub(in crate::checker) fn defined_functions(
    defines: &[crate::corpus::proof::InScope],
) -> Vec<Defined> {
    let mut functions = Vec::new();
    for s in defines {
        let d = s.define;
        match &*s.parts {
            DefineParts::Recursion(r) => {
                for name in &r.names {
                    functions.push(Defined {
                        name: name.clone(),
                        label: s.label.clone(),
                        domains: vec![d.formula(&r.domain)],
                        recursive: true,
                    });
                }
            }
            DefineParts::One(one) if !one.params.is_empty() => {
                functions.push(Defined {
                    name: s.name.clone(),
                    label: s.label.clone(),
                    domains: one.params.iter().map(|p| d.domain(p)).collect(),
                    recursive: false,
                });
            }
            _ => {}
        }
    }
    functions
}

/// Whether a requires line claims `f is a function on A`, the one fact a
/// define it names gives without a line saying it.
pub(super) fn claims_function_on(req: &Requires, known: &Known) -> bool {
    known
        .whole_as_written(&req.fact)
        .is_some_and(|claim| claim.notation() == FUNCTION_ON)
}

/// Why a requires line `f is a function on A`, from a define it names, is
/// not given by it: a define gives a function on the one domain it writes,
/// as a map of one argument, which the build proves it on (`define_on`), so
/// f is to be such a function of a define the line names and A that domain.
/// None where it is, and for a line claiming anything else.
pub(super) fn function_on_unshown(
    thm: &Theorem,
    req: &Requires,
    known: &Known,
    scopes: &[FileScope],
) -> Option<String> {
    let claim = known.whole_as_written(&req.fact)?;
    let (FUNCTION_ON, [function, on]) = (claim.notation(), claim.children.as_slice())
    else {
        return None;
    };
    let named = req.lines();
    let defines = proof::in_scope(thm, scopes);
    let given = defined_functions(&defines).into_iter().find_map(|f| {
        let label = f.label.clone()?;
        (f.name == function.text && named.contains(&label)).then_some((f, label))
    });
    let Some((given, label)) = given else {
        return Some(format!(
            "no define it names gives {}",
            known.print(function)
        ));
    };
    // A sequence by recursion is a map of one argument, its index, on the
    // set the index runs over.
    let [domain] = given.domains.as_slice() else {
        return Some(format!(
            "{} gives {} of {} arguments, and a function on one domain is a map of one argument",
            label,
            known.print(function),
            given.domains.len()
        ));
    };
    let domain = known.read_as_written(&domain.formula().ok()?)?;
    (!known.alike(&domain, on)).then(|| {
        format!(
            "{} gives {} on {}",
            label,
            known.print(function),
            known.print(&domain)
        )
    })
}

/// One argument a defined function is applied to in a claim, and the
/// facts any one of which says it is in the function's domain, as written.
pub(in crate::checker) struct Applied {
    pub(super) label: String,
    pub(super) arg: Node,
    pub(super) says: Vec<Node>,
}

/// The applications whose domains a step citing a define asks. A step whose
/// reason is the define itself evaluates the function where an application
/// is a whole side of its equation, as `s(s(a)) = (s(a) + 1) mod 10`
/// evaluates s at s(a); an application elsewhere in the claim, the s(a)
/// inside, is a term carried as it stands and asks nothing. Any other step
/// citing the define asks of every application in its claim.
pub(super) fn evaluated(
    step: &Step,
    used: &[Defined],
    known: &Known,
    library: &Library,
) -> Vec<Applied> {
    let direct = step.just.head == Head::Define
        && used
            .iter()
            .any(|f| f.label.is_some() && step.just.defined == f.label);
    let Some(claim) = known.whole_as_written(&step.claim) else {
        return Vec::new(); // `check_formulas` says it does not read
    };
    let mut out = if !(direct
        && claim.children.len() == 2
        && library.ctx.equations.contains(&claim.notation()))
    {
        applied(used, &claim, false, known)
    } else {
        claim
            .children
            .iter()
            .flat_map(|side| applied(used, side, true, known))
            .collect()
    };
    out.extend(applied_in_cited(step, used, known, &library.ctx));
    out
}

/// The applications of the functions in the lines a step cites beside
/// their define: a line saying u ∈ I(k), read through the define of I, says
/// u is in what I's rule gives at k, which holds where k is in I's domain,
/// as it does of an application the claim writes. An application at a
/// letter the line binds, q(j) under a sum over j or S(n) in a limit as
/// n → ∞, is said of every value the binder gives it, and asks nothing of
/// one.
pub(super) fn applied_in_cited(
    step: &Step,
    used: &[Defined],
    known: &Known,
    ctx: &Context,
) -> Vec<Applied> {
    let scope = known.scope(step);
    let mut out = Vec::new();
    for r in &step.just.refs {
        if used.iter().any(|f| f.label.as_ref() == Some(r)) {
            continue;
        }
        let Some(stated) = scope.get(r.as_str()) else {
            continue;
        };
        for part in known.sentences(stated) {
            let mut bound = BTreeSet::new();
            letters_bound(&part, ctx, &mut bound);
            out.extend(
                applied(used, &part, false, known)
                    .into_iter()
                    .filter(|asked| asked.arg.names().is_disjoint(&bound)),
            );
        }
    }
    out
}

/// Every letter a binder anywhere in a formula binds, by the places the
/// notation database declares each binder holds its letters in.
pub(in crate::checker) fn letters_bound(
    node: &Node,
    ctx: &Context,
    out: &mut BTreeSet<String>,
) {
    let (held, _) = ctx.held_body(node.notation());
    for at in held {
        if let Some(letter) = node.children.get(at).filter(|c| c.is_name()) {
            out.insert(letter.text.to_string());
        }
    }
    for child in &node.children {
        letters_bound(child, ctx, out);
    }
}

/// Every application of the functions in `claim`, a tree as written, each
/// argument with what says it is in its domain; where `leading`, only an
/// application the claim begins with, as `s(s(a))` begins with the outer s
/// and `f(x) + 1` with f(x).
pub(super) fn applied(
    functions: &[Defined],
    claim: &Node,
    leading: bool,
    known: &Known,
) -> Vec<Applied> {
    let nodes: Vec<Node> = if leading {
        let mut spine = vec![claim.clone()];
        while let Some(first) = spine.last().and_then(|n| n.children.first().cloned()) {
            spine.push(first);
        }
        spine
    } else {
        claim.walk()
    };
    // A domain that does not read is `check_formulas`'s to report.
    let read = |w: &Written| known.read_as_written(&w.formula().ok()?);
    let (g, sorts) = (known.env.g, &known.sorts);
    let mut out = Vec::new();
    for Defined {
        name,
        label,
        domains,
        recursive,
    } in functions
    {
        // An import that gives no label is one no line cites.
        let Some(label) = label else {
            continue;
        };
        for node in &nodes {
            let [function, args @ ..] = node.children.as_slice() else {
                continue;
            };
            if !matches!(node.notation(), APPLICATION | APPLICATION_TO_TWO)
                || !function.is_name()
                || &function.text != name
                || args.len() != domains.len()
            {
                continue;
            }
            for (arg, domain) in args.iter().zip(domains) {
                // A recursion's step at m asks m; any other argument is its
                // value at 0, which asks nothing.
                let member = if *recursive {
                    match (arg.spelling(), arg.children.as_slice()) {
                        (PLUS, [index, one])
                            if one.notation() == NUMERAL && one.text == "1" =>
                        {
                            index.clone()
                        }
                        _ => continue,
                    }
                } else {
                    arg.clone()
                };
                let Some(set) = read(domain) else {
                    continue;
                };
                let within = |form: &'static str, set: &Node| {
                    page::filled(form, g, sorts, &[("x", &member), ("S", set)]).ok()
                };
                let mut says: Vec<Node> = within("x ∈ S", &set).into_iter().collect();
                // A power set's member is a part, which the page may say with
                // ⊆: `for X ⊆ A` asks C ⊆ A of M(C).
                if let (POWERSET, [inner]) = (set.notation(), set.children.as_slice()) {
                    says.extend(within("x ⊆ S", inner));
                }
                if says.is_empty() {
                    continue;
                }
                out.push(Applied {
                    label: label.clone(),
                    arg: arg.clone(),
                    says,
                });
            }
        }
    }
    out
}

/// Whether `arg` is the index of a sequence's limit in `formulas`, n of S(n)
/// → K as n → ∞.
pub(super) fn limit_index(formulas: &[Node], arg: &Node) -> bool {
    formulas.iter().flat_map(|f| f.walk()).any(|n| {
        n.notation() == TENDS_TO
            && matches!(n.children.as_slice(), [_, _, k] if k.is_name() && k.text == arg.text)
    })
}

/// The applications of `used` the lines a step cites besides their defines
/// make at a letter they bind, each with the sentence it stands in: S(n) of
/// a cited `S(n) → K as n → ∞`, which `applied_in_cited` leaves to
/// `index_range_within`.
pub(super) fn applied_at_bound_in_cited(
    step: &Step,
    used: &[Defined],
    known: &Known,
    ctx: &Context,
) -> Vec<(Applied, Node)> {
    let scope = known.scope(step);
    let mut out = Vec::new();
    for r in &step.just.refs {
        if used.iter().any(|f| f.label.as_ref() == Some(r)) {
            continue;
        }
        let Some(stated) = scope.get(r.as_str()) else {
            continue;
        };
        for part in known.sentences(stated) {
            let mut bound = BTreeSet::new();
            letters_bound(&part, ctx, &mut bound);
            out.extend(
                applied(used, &part, false, known)
                    .into_iter()
                    .filter(|asked| !asked.arg.names().is_disjoint(&bound))
                    .map(|asked| (asked, part.clone())),
            );
        }
    }
    out
}

/// The applications a step citing a define makes at the index of a sum or
/// a sequence's limit, in its claim or a line it cites, whose range is not
/// inside the define's domain, each with that domain: Σ(k = 0 to n) t(k) of
/// a t on ℕ, whose rule says nothing of t(0).
fn indices_outside(
    step: &Step,
    functions: &[Defined],
    known: &Known,
    library: &Library,
) -> Vec<(Applied, Node)> {
    let used: Vec<Defined> = functions
        .iter()
        .filter(|f| f.label.as_ref().is_some_and(|l| step.just.refs.contains(l)))
        .cloned()
        .collect();
    if used.is_empty() {
        return Vec::new();
    }
    let Some(claim) = known.whole_as_written(&step.claim) else {
        return Vec::new();
    };
    let letters = super::super::library::introduced(known, step);
    let in_claim = evaluated(step, &used, known, library)
        .into_iter()
        .map(|asked| (asked, claim.clone()));
    in_claim
        .chain(applied_at_bound_in_cited(step, &used, known, &library.ctx))
        .filter_map(|(asked, formula)| {
            let domain = asked.says.first()?.children.get(1)?.clone();
            let within = index_range_within(
                slice::from_ref(&formula),
                &asked.arg,
                &domain,
                &letters,
                known,
                &library.ctx,
            );
            (within == Some(false)).then_some((asked, domain))
        })
        .collect()
}

/// Whether `arg` is the index of a sum or a sequence's limit in `formulas`
/// whose range lies inside `domain`: t(k) in Σ(k = 1 to n) t(k) of a t on ℕ
/// is, and in Σ(k = 0 to n) t(k) is not, as {0, …, n} holds 0; S(n) in S(n)
/// → K as n → ∞ is where the domain holds ℕ, which a sequence's index runs
/// over. None where `arg` is no such index there, or the range or the
/// domain is no set whose numbers the page says once.
pub(super) fn index_range_within(
    formulas: &[Node],
    arg: &Node,
    domain: &Node,
    letters: &Introduced,
    known: &Known,
    ctx: &Context,
) -> Option<bool> {
    if !arg.is_name() {
        return None;
    }
    // A sequence's index, n of S(n) → K as n → ∞, runs over ℕ (the
    // notation's own reading).
    if limit_index(formulas, arg) {
        let inside = citing::set_system(domain, letters)?;
        return Some(System::N.within(inside));
    }
    let sum = formulas.iter().flat_map(|f| f.walk()).find(|n| {
        ctx.sums.contains(&n.notation())
            && matches!(n.children.as_slice(), [k, _, _, _] if k.is_name() && k.text == arg.text)
    })?;
    let [_, from, to, _] = sum.children.as_slice() else {
        return None;
    };
    let range = page::filled(
        "{a, …, b}",
        known.env.g,
        &known.sorts,
        &[("a", from), ("b", to)],
    )
    .ok()?;
    let runs = citing::range_system(&range)?;
    let inside = citing::set_system(domain, letters)?;
    Some(runs.within(inside))
}

/// The indices of the sums anywhere in a formula, by the places the
/// notation database declares each sum holds its index in.
pub(super) fn sum_indices(node: &Node, ctx: &Context, out: &mut BTreeSet<String>) {
    if ctx.sums.contains(&node.notation()) {
        let (held, _) = ctx.held_body(node.notation());
        for at in held {
            if let Some(letter) = node.children.get(at).filter(|c| c.is_name()) {
                out.insert(letter.text.to_string());
            }
        }
    }
    for child in &node.children {
        sum_indices(child, ctx, out);
    }
}

/// A define used for what it is has each argument in its domain.
///
/// `define S(m) := Σ(j = 1 to m) j, for m ∈ ℕ` gives S(k + 1) its rule only
/// where k + 1 ∈ ℕ, so a step citing the define, itself or on a calculation
/// line, writes a requires line for each argument's domain it does not
/// otherwise have (`SYNTAX.md`). A built-up argument is no exception, as an
/// item's hypothesis of one is not: what is cited or required says it, with
/// what each of those implies.
pub fn check_define_domains(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
    scopes: &[FileScope],
) {
    let functions = defined_functions(&proof::in_scope(thm, scopes));
    if functions.is_empty() {
        return;
    }
    let needs = |asked: &Applied| known.print(&asked.says[0]);
    for step in &thm.steps {
        for (asked, domain) in indices_outside(step, &functions, known, library) {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} applies {} at {}, the index of a sum or a sequence whose range is not inside {}, the domain {} gives it on",
                    step.number,
                    asked.label,
                    known.print(&asked.arg),
                    known.print(&domain),
                    asked.label,
                ),
            );
        }
        for asked in domains_unsaid(step, &functions, known, library) {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} cites {} at {}, so it needs {}, and nothing it cites or requires says it",
                    step.number,
                    asked.label,
                    known.print(&asked.arg),
                    needs(&asked)
                ),
            );
        }
        // A requires line whose reason is a method or an item is the step it
        // would be, and cites a define as a step does.
        for req in &step.requires {
            let Some(as_step) = requires_read_as_step(step, req) else {
                continue;
            };
            for asked in domains_unsaid(&as_step, &functions, known, library) {
                report.say(
                    &thm.path,
                    req.line,
                    format!(
                        "the requires line {} of {} cites {} at {}, so it needs {}, and nothing it cites or the requires lines above it say it",
                        str::trim(req.fact.text()),
                        step.called(),
                        asked.label,
                        known.print(&asked.arg),
                        needs(&asked)
                    ),
                );
            }
        }
    }
}

/// A member of a difference is a member of the set taken from: `x ∈ V ∖
/// {v(0)}` says x ∈ V, as the build reads it (`eldifi`, among its membership
/// lemmas). None for any other fact.
pub(super) fn member_taken_from(fact: &Node, library: &Library) -> Option<Node> {
    let (MEMBERSHIP, [member, set]) = (fact.notation(), fact.children.as_slice())
    else {
        return None;
    };
    let ([from, _], true) = (set.children.as_slice(), set.spelling() == WITHOUT) else {
        return None;
    };
    Some(page::made(
        library.env.g,
        IN,
        vec![member.clone(), from.clone()],
    ))
}

/// Each application of a define in what a theorem states, sentence by
/// sentence, with what says its argument is in the define's domain. An
/// argument holding a letter the statement binds is left out: its binder
/// says where it lies. A sequence by recursion is not written out by a rule
/// (`sorts::statement_definitions`), and asks nothing here. A sentence that
/// does not read is `check_formulas`'s to report.
pub(super) fn stated_applications(
    functions: &[Defined],
    written: &Written,
    known: &Known,
    library: &Library,
) -> Vec<Applied> {
    let functions: Vec<Defined> =
        functions.iter().filter(|f| !f.recursive).cloned().collect();
    let mut out = Vec::new();
    for stated in written
        .sentences()
        .iter()
        .filter_map(|s| known.read_as_written(s))
    {
        let mut bound = BTreeSet::new();
        letters_bound(&stated, &library.ctx, &mut bound);
        out.extend(
            applied(&functions, &stated, false, known)
                .into_iter()
                .filter(|a| a.arg.names().is_disjoint(&bound)),
        );
    }
    out
}

/// The applications a step citing a theorem of its own file may read with
/// the defines that theorem is stated over (`sorts::stated_over`): the
/// theorem speaks of them by name, as the step's claim and the lines it
/// cites do, and its statement is the rules written out at the step's
/// arguments, which holds where each is in its define's domain. A line
/// saying one of those domains does work: `ballot-recurrence` cited from a
/// line applying G at m − 1 is read there where m − 1 ∈ ℕ₀. Not every
/// application is read so, D(f(n), n) passed whole as the argument of a
/// theorem stated over s asks nothing of f(n), so none is demanded here.
/// None for a step citing no such theorem.
pub(super) fn read_over_cited_theorem(
    thm: &Theorem,
    step: &Step,
    scopes: &[FileScope],
    known: &Known,
) -> Vec<Applied> {
    let Some(item) = step.just.cited_item() else {
        return Vec::new();
    };
    let over = sorts::stated_over(thm, scopes, &step.just.item(&item));
    if over.is_empty() {
        return Vec::new();
    }
    let functions: Vec<Defined> = defined_functions(&proof::in_scope(thm, scopes))
        .into_iter()
        .filter(|f| !f.recursive && f.label.as_ref().is_some_and(|l| over.contains(l)))
        .collect();
    let Some(claim) = known.whole_as_written(&step.claim) else {
        return Vec::new(); // `check_formulas` says it does not read
    };
    let mut out = applied(&functions, &claim, false, known);
    out.extend(applied_in_cited(step, &functions, known, known.ctx));
    out
}

/// Where a theorem's statement applies a define it is written out
/// (`ELABORATION.md`, a definition from outside the theorem), and the steps
/// speak of the name. A step naming a hypothesis, in its `from` or as the
/// line a substitute is put into, reads it with the name, as its rule at the
/// arguments the hypothesis applies it to, and that holds only where each is
/// in the define's domain. So the step asks it of what it cites or requires,
/// as a step citing the define does (`check_define_domains`): a step naming
/// `|G(m − 1, n)|·x = y`, with G on ℕ₀, asks m − 1 ∈ ℕ₀.
pub fn check_stated_domains(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
    scopes: &[FileScope],
) {
    let functions = defined_functions(&proof::in_scope(thm, scopes));
    if functions.is_empty() {
        return;
    }
    for step in &thm.steps {
        let into = step.just.into.as_ref().map(|p| p.named().to_string());
        let mut asked: Vec<Applied> = Vec::new();
        for label in step.just.refs.iter().chain(into.as_ref()) {
            let hypothesis = thm
                .hypotheses
                .iter()
                .find(|h| h.label.as_deref() == Some(label.as_str()));
            if let Some(h) = hypothesis {
                asked.extend(stated_applications(
                    &functions,
                    &h.body(&thm.path),
                    known,
                    library,
                ));
            }
        }
        for asked in unsaid_by(step, asked, known, library) {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} reads a hypothesis applying the define {} at {}, which the statement writes out, so it needs {}, and nothing it cites or requires says it",
                    step.number,
                    asked.label,
                    known.print(&asked.arg),
                    known.print(&asked.says[0])
                ),
            );
        }
    }
}

/// A theorem stated over a define writes it out (`SYNTAX.md`, "The
/// statement means its define written out"), so a step citing it meets what
/// the theorem asks and concludes, at the step's arguments, only where each
/// argument the statement applies the define to is in its domain:
/// ballot-recurrence asks for the formula at G(m − 1, n), with G on ℕ₀, and
/// a step citing it at m asks m − 1 ∈ ℕ₀. So the step asks it of what it
/// cites or requires, as a step citing the define does
/// (`check_define_domains`). An argument holding a letter the statement
/// binds is left out: its binder says where it lies.
pub fn check_cited_domains(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
    scopes: &[FileScope],
) {
    let functions = defined_functions(&proof::in_scope(thm, scopes));
    if functions.is_empty() {
        return;
    }
    for step in &thm.steps {
        let Some(item) = step.just.cited_item() else {
            continue;
        };
        let over = sorts::stated_over(thm, scopes, &step.just.item(&item));
        let used: Vec<Defined> = functions
            .iter()
            .filter(|f| {
                !f.recursive && f.label.as_ref().is_some_and(|l| over.contains(l))
            })
            .cloned()
            .collect();
        if used.is_empty() {
            continue;
        }
        let Some(read) = cited(step, library, known) else {
            continue; // the citation's own checks say why it does not read
        };
        // The statement as its page writes it, the define by name: what the
        // build reads written out.
        let Some(Item::Theorem(of)) = library.item(&read.item) else {
            continue;
        };
        let written: Vec<Written> = of
            .hypotheses
            .iter()
            .map(|h| h.body(&of.path))
            .chain([of.stated()])
            .collect();
        let stated: Vec<Node> = written
            .iter()
            .flat_map(|w| w.sentences())
            .filter_map(|s| known.read_as_written(&s))
            .collect();
        let mut asked = Vec::new();
        for said in &stated {
            let mut bound = BTreeSet::new();
            letters_bound(said, &library.ctx, &mut bound);
            let at = filled(said, &read.binding, &library.ctx);
            asked.extend(
                applied(&used, &at, false, known)
                    .into_iter()
                    .filter(|a| a.arg.names().is_disjoint(&bound)),
            );
        }
        // The kernel reads the argument written out as well, s(s(t)) as s
        // at (t + 1) mod 10, and a membership `membership` builds of that
        // from what the step cites is asked of no line.
        let defined = known.citing_step(step);
        let facts: Vec<Node> = known
            .parts(step, library)
            .facts
            .iter()
            .map(|f| known.as_cited(f, &defined))
            .collect();
        let asked: Vec<Applied> = asked
            .into_iter()
            .filter(|a| {
                let written = known.as_cited(&a.says[0], &defined);
                !built_from(&written, &facts, step, known, library)
            })
            .collect();
        for asked in unsaid_by(step, asked, known, library) {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} cites {}, whose statement applies the define {} at {} and is written out, so it needs {}, and nothing it cites or requires says it",
                    step.number,
                    item,
                    asked.label,
                    known.print(&asked.arg),
                    known.print(&asked.says[0])
                ),
            );
        }
    }
}

/// Whether `fact`, a membership in a number system, is one `membership`
/// would build from what `step` cites (`methods::membership::holds`): its
/// parts in the system by the letters, the function types in scope and
/// `facts`, as (t + 1) mod 10 ∈ ℤ is where a cited line says t ∈ ℤ. The
/// build proves such a membership from the same facts.
pub(super) fn built_from(
    fact: &Node,
    facts: &[Node],
    step: &Step,
    known: &Known,
    library: &Library,
) -> bool {
    let (MEMBERSHIP, [term, set]) = (fact.notation(), fact.children.as_slice()) else {
        return false;
    };
    let Some(system) = (set.notation() == NUMBER_SYSTEMS)
        .then(|| System::of_sign(&set.text))
        .flatten()
    else {
        return false;
    };
    let mut typed = typed_in_scope(known, step);
    typed.extend(facts.iter().filter(|f| types_a_function(f)).cloned());
    let given = crate::methods::membership::Facts {
        facts,
        letters: super::super::library::introduced(known, step),
        ranged: IndexMap::new(),
        typed: &typed,
        in_sums: &typed,
        targets: &library.targets,
        ctx: known.ctx,
    };
    membership::holds(term, system, &given)
}

/// The last step's claim speaks of a define's name where the statement
/// writes the define out (`check_stated_domains`), and the theorem is the
/// last step carried to its statement, which reads the name as its rule at
/// each argument the conclusion applies it to. That holds only where each
/// argument is in the define's domain, and the carrying is the theorem's,
/// not a step's: it reads what the proof holds at its outermost level, its
/// hypotheses, its unnumbered steps' claims and what the page says once.
/// So one of those says it: add-last-place states G(m − 1, n), with G on
/// ℕ₀, and a line of its proof says m − 1 ∈ ℕ₀. A requires line is no such
/// line: it holds for its own step only.
pub fn check_conclusion_domains(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
    scopes: &[FileScope],
) {
    let functions = defined_functions(&proof::in_scope(thm, scopes));
    if functions.is_empty() {
        return;
    }
    // A theorem proved `by` a method holds every step in that method's
    // block, so what it holds at its outermost level is its hypotheses.
    let by_method = thm.steps.first().filter(|s| s.proves_theorem());
    let last = match by_method {
        Some(theorem) => Some(theorem),
        None => thm.steps.iter().rev().find(|s| s.number.depth() == 1),
    };
    let Some(last) = last else {
        return; // `check_last_step` says there is none
    };
    let asked = stated_applications(&functions, &thm.stated(), known, library);
    if asked.is_empty() {
        return;
    }
    let mut outermost = last.clone();
    outermost.requires = Vec::new();
    outermost.just.refs = thm
        .hypotheses
        .iter()
        .filter_map(|h| h.label.clone().filter(|l| !l.is_empty()))
        .chain(
            thm.steps
                .iter()
                .filter(|s| by_method.is_none() && s.number.depth() == 1)
                .map(|s| s.number.to_string()),
        )
        .collect();
    for asked in unsaid_by(&outermost, asked, known, library) {
        report.say(
            &thm.path,
            thm.conclusion_line,
            format!(
                "the conclusion of {} applies the define {} at {} and is written out, so it needs {}, and neither a hypothesis nor a line of its proof outside a block says it",
                thm.name,
                asked.label,
                known.print(&asked.arg),
                known.print(&asked.says[0])
            ),
        );
    }
}

/// A requires line whose reason is a method or an item, read as the step it
/// would be (`requires_as_step`), with the requires lines above it as its
/// own, since it rests on them (`ELABORATION.md`, R2); None for a reason
/// that is only `from`, which is read from the lines it names, and for one
/// the skeleton reader could not cut, which `check_reason` reports.
pub(super) fn requires_read_as_step(step: &Step, req: &Requires) -> Option<Step> {
    let Ok(by) = &req.by else {
        return None;
    };
    if !matches!(by.head, Head::Method(_) | Head::Item { .. }) {
        return None;
    }
    let mut as_step = reason_as_step(step, req, by);
    as_step.requires = step.requires_above(req.line).cloned().collect();
    Some(as_step)
}

/// What a step citing a define, itself or on a calculation line, needs of
/// each argument's domain and nothing it cites or requires says, with what
/// each of those implies: each application once.
pub(in crate::checker) fn domains_unsaid(
    step: &Step,
    functions: &[Defined],
    known: &Known,
    library: &Library,
) -> Vec<Applied> {
    let links = chain_links(&step.just, &known.thm.path);
    let mut cited: BTreeSet<String> = step.just.refs.iter().cloned().collect();
    cited.extend(
        links
            .iter()
            .filter_map(|l| l.line.cited())
            .map(String::from),
    );
    let used: Vec<Defined> = functions
        .iter()
        .filter(|f| f.label.as_ref().is_some_and(|l| cited.contains(l)))
        .cloned()
        .collect();
    if used.is_empty() {
        return Vec::new();
    }
    unsaid_by(step, evaluated(step, &used, known, library), known, library)
}

/// Of the applications `asked`, each whose domain nothing `step` cites or
/// requires says, with what each of those implies: each application once.
pub(super) fn unsaid_by(
    step: &Step,
    asked: Vec<Applied>,
    known: &Known,
    library: &Library,
) -> Vec<Applied> {
    let links = chain_links(&step.just, &known.thm.path);
    let parts = known.read_out_parts(step, library);
    let mut facts = parts.facts.clone();
    let from_links: Vec<String> = links
        .iter()
        .filter_map(|l| l.line.cited())
        .map(String::from)
        .collect();
    let refs: Vec<&str> = from_links.iter().map(String::as_str).collect();
    facts.extend(known.lines_say(step, &refs));
    // A claim said of every member puts the member in its domain.
    facts.extend(
        parts
            .claims
            .iter()
            .filter_map(|c| claimed_member(c, library.env.g))
            .map(|(member, _)| member),
    );
    let taken: Vec<Node> = facts
        .iter()
        .filter_map(|f| member_taken_from(f, library))
        .collect();
    facts.extend(taken);
    let facts =
        finished(facts, Vec::new(), Binding::new(), library, &known.sorts).facts;
    // A sum's index is in the range the sum runs over, and what holds it is a
    // term of the sum, whose values are a family's (`family_asks`).
    let mut indices: BTreeSet<String> = BTreeSet::new();
    for claim in &parts.claims {
        sum_indices(claim, &library.ctx, &mut indices);
    }
    let shapes: FxIndexSet<ByShape> = facts.iter().map(Node::by_shape).collect();
    let defined = known.citing_step(step);
    let mut seen: FxIndexSet<ByShape> = FxIndexSet::default();
    let mut out = Vec::new();
    for asked in asked {
        if !asked.arg.names().is_disjoint(&indices) {
            continue;
        }
        // Compared with the facts as they are read, defines written out.
        let said = asked
            .says
            .iter()
            .any(|s| shapes.contains(&known.as_cited(s, &defined).by_shape()));
        if said || !seen.insert(asked.says[0].by_shape()) {
            continue;
        }
        out.push(asked);
    }
    out
}
