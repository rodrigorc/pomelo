use std::borrow::Cow;
use std::cell::RefCell;
use std::cmp::{self, Ordering};
use std::collections::{BTreeSet, HashMap};
use std::fmt::{Display, Write};
use std::hash::{Hash, Hasher};

use crate::decl::*;
use proc_macro2::{Literal, Span, TokenStream};
use quote::ToTokens;
use syn::{
    spanned::Spanned, Attribute, Block, Fields, Ident, Item, ItemEnum, ItemStruct, Pat, Type,
    Variant,
};

mod vecref;
use vecref::*;

type RuleSet = BTreeSet<usize>;

enum NewSymbolType {
    Terminal,
    NonTerminal,
    MultiTerminal,
}

#[derive(Debug, Copy, Clone)]
struct Precedence(i32, Associativity);

fn precedence_cmp(a: Precedence, b: Precedence) -> Ordering {
    match a.0.cmp(&b.0) {
        Ordering::Equal => match a.1 {
            Associativity::Left => Ordering::Less,
            Associativity::Right => Ordering::Greater,
            Associativity::None => Ordering::Equal,
        },
        o => o,
    }
}

type SymbolId = VecRefId<Symbol>;
type StateId = VecRefId<State>;
type RuleId = VecRefId<Rule>;
type ConfigId = VecRefId<Config>;

//Symbols do not have a single point of definition, instead they can appear in many places,
//thus, its Span is not in struct Symbol, but in some selected references, those created directly
//in the Rule
#[derive(Debug, Clone)]
struct SymbolSpan(SymbolId, Span);

//In RHS of a rule, we have symbols, spans and possibly alias
#[derive(Debug, Clone)]
struct SymbolAlias(SymbolId, Span, Option<Pat>);

#[derive(Debug)]
struct Rule {
    span: Span,
    lhs: SymbolSpan,                //Left-hand side of the rule
    lhs_start: bool,                //True if LHS is the start symbol
    rhs: Vec<SymbolAlias>,          //RHS symbols and aliases
    code: Option<Block>,            //The code executed when this rule is reduced
    prec_sym: Option<SymbolId>,     //Precedence symbol for this rule
    precedence: Option<Precedence>, //Actual precedence for this rule
    index: usize,                   //An index number for this rule
    can_reduce: bool,               //True if this rule is ever reduced
}

#[derive(Debug)]
enum SymbolType {
    Terminal,
    NonTerminal {
        rules: Vec<RuleId>, //List of rules, if a NonTerminal
        first_set: RuleSet, //First-set for all rules of this symbol
        lambda: bool,       //True if NonTerminal and can generate an empty string
    },
    MultiTerminal(Vec<SymbolId>), //constituent symbols if MultiTerminal
}
use SymbolType::*;

#[derive(Debug)]
struct Symbol {
    name: String,                   //Name of the symbol
    index: usize,                   //Index number for this symbol
    typ: SymbolType,                //Either Terminal or NonTerminal
    fallback: Option<SymbolId>,     //Fallback token in case this token desn't parse
    precedence: Option<Precedence>, //Precedence
    use_cnt: i32,                   //Number of times used
    data_type: Option<Type>,        //Data type held by this object
    dt_num: usize, //The data type number (0 is always ()). The YY{} element of stack is the correct data type for this object
    attributes: Vec<Attribute>,
}

impl Symbol {
    fn is_lambda(&self) -> bool {
        match self.typ {
            NonTerminal { lambda, .. } => lambda,
            _ => false,
        }
    }
    fn get_non_terminal_rules(&self) -> Option<&[RuleId]> {
        match &self.typ {
            NonTerminal { rules, .. } => Some(rules),
            _ => None,
        }
    }
}

impl Hash for Symbol {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

/* A configuration is a production rule of the grammar together with
* a mark (dot) showing how much of that rule has been processed so far.
* Configurations also contain a follow-set which is a list of terminal
* symbols which are allowed to immediately follow the end of the rule.
* Every configuration is recorded as an instance of the following: */
#[derive(Debug)]
enum CfgStatus {
    Complete,
    Incomplete,
}

#[derive(Debug)]
struct Config {
    rule: RuleId,        //The rule upon which the configuration is based
    dot: usize,          //The parse point
    fws: RuleSet,        //Follow-set for this configuration only
    fplp: Vec<ConfigId>, //Follow-set forward propagation links
    bplp: Vec<ConfigId>, //Follow-set backwards propagation links
    status: CfgStatus,   //Used during followset and shift computations
}

fn config_cmp_key(data: &Pomelo, a: ConfigId, index: usize, dot: usize) -> Ordering {
    let adot = data.the_configs.get(a).dot;
    let aindex = data.the_rules.get(data.the_configs.get(a).rule).index;
    (aindex, adot).cmp(&(index, dot))
}

fn config_cmp(data: &Pomelo, a: ConfigId, b: ConfigId) -> Ordering {
    let bdot = data.the_configs.get(b).dot;
    let bindex = data.the_rules.get(data.the_configs.get(b).rule).index;
    config_cmp_key(data, a, bindex, bdot)
}

#[derive(Debug, Clone)]
enum ActionDetail {
    Shift(StateId),
    Accept,
    Reduce(RuleId),
    Error,
    SSConflict(StateId), //A shift/shift conflict
    SRConflict(RuleId),  //Was a reduce, but part of a conflict
    RRConflict(RuleId),  //Was a reduce, but part of a conflict
    SHResolved(StateId), //Was a shift. Associativity resolved conflict
    RDResolved(RuleId),  //Was reduce. Associativity resolved conflict
    NotUsed,             //Deleted by compression
}

impl ActionDetail {
    fn cmp(
        the_states: &VecRef<State>,
        the_rules: &VecRef<Rule>,
        a: &ActionDetail,
        b: &ActionDetail,
    ) -> Ordering {
        use ActionDetail::*;
        match a {
            Shift(sa) => match b {
                Shift(sb) => the_states
                    .get(sa)
                    .state_num
                    .cmp(&the_states.get(sb).state_num),
                _ => Ordering::Less,
            },
            Accept => match b {
                Shift(_) => Ordering::Greater,
                Accept => Ordering::Equal,
                _ => Ordering::Less,
            },
            Reduce(ra) => match b {
                Shift(_) => Ordering::Greater,
                Accept => Ordering::Greater,
                Reduce(rb) => the_rules.get(ra).index.cmp(&the_rules.get(rb).index),
                _ => Ordering::Less,
            },
            _ => Ordering::Equal,
        }
    }
}

//Every shift or reduce operation is stored as one of the following
#[derive(Debug)]
struct Action {
    look_ahead: SymbolId, //The look-ahead symbol
    detail: ActionDetail,
}

fn action_cmp(
    the_symbols: &VecRef<Symbol>,
    the_states: &VecRef<State>,
    the_rules: &VecRef<Rule>,
    a: &RefCell<Action>,
    b: &RefCell<Action>,
) -> Ordering {
    let a = a.borrow();
    let b = b.borrow();
    let rc = the_symbols
        .get(a.look_ahead)
        .index
        .cmp(&the_symbols.get(b.look_ahead).index);
    match rc {
        Ordering::Equal => ActionDetail::cmp(the_states, the_rules, &a.detail, &b.detail),
        rc => rc,
    }
}

#[derive(Debug)]
struct State {
    configs: Vec<ConfigId>,        //All configurations in this set
    basis: Vec<ConfigId>,          //The basis configuration for this state
    state_num: usize,              //Sequential number for this state
    actions: Vec<RefCell<Action>>, //Array of actions for this state
    n_tkn_act: i32,                //number of actions on terminals and non-terminals
    n_nt_act: i32,
    i_tkn_ofst: Option<i32>, //yy_action[] offset for terminals and non-terminals
    i_nt_ofst: Option<i32>,
    i_dflt: usize, //Default action
}

#[derive(Debug)]
pub struct Pomelo {
    the_symbols: VecRef<Symbol>, //Unsorted array of symbols
    the_states: VecRef<State>,   //Unsorted list of states
    the_rules: VecRef<Rule>,     //Unsorted list of all rules
    the_configs: VecRef<Config>, //Unsorted list of configs,
    module: Ident,
    includes: Vec<Item>,
    syntax_error: Option<Block>,
    parse_fail: Option<Block>,
    stack_overflow: Option<Block>,
    token_enum: Option<ItemEnum>, //The enum Token{}, if specified with %token
    parser_struct: Option<ItemStruct>, //The struct Parser{}, if specified with %parser
    states: Vec<StateId>,         //Table of states sorted by state number
    rules: Vec<RuleId>,           //List of all rules
    default_index: usize,         //The index of the default symbol (always the last one in symbols)
    num_terminals: usize,         //symbols[0..num_terminals] are the terminal symbols
    symbols: Vec<SymbolId>,       //Sorted array of symbols
    error_symbol: SymbolId,       //The error symbol
    wildcard: Option<SymbolId>,   //The symbol that matches anything
    arg: Option<Type>,            //Declaration of the extra argument to parser
    err_type: Option<Type>,       //Declaration of the error type of the parser
    nconflict: i32,               //Number of parsing conflicts
    has_fallback: bool,           //True if any %fallback is seen in the grammar
    default_type: Option<Type>,   //The %default_type
    start: Option<SymbolId>,
    optional_tokens: HashMap<SymbolId, SymbolSpan>,
    extra_token: Option<Type>,
    stack_type: Option<Type>,
    stack_limit: usize,
    verbose: bool,
}

struct ParserData {
    precedence: i32,
}

#[derive(Debug)]
struct AxSet {
    stp: StateId,  // A pointer to a state
    is_tkn: bool,  // true for tokens, false for non-terminals
    n_action: i32, // Number of actions
}

/*
** The state of the yy_action table under construction is an instance of
** the following structure.
**
** The yy_action table maps the pair (state_number, lookahead) into an
** action_number.  The table is an array of integers pairs.  The state_number
** determines an initial offset into the yy_action array.  The lookahead
** value is then added to this initial offset to get an index X into the
** yy_action array. If the aAction[X].lookahead equals the value of the
** of the lookahead input, then the value of the action_number output is
** aAction[X].action.  If the lookaheads do not match then the
** default action for the state_number is returned.
**
** All actions associated with a single state_number are first entered
** into aLookahead[] using multiple calls to acttab_action().  Then the
** actions for that single state_number are placed into the aAction[]
** array with a single call to acttab_insert().  The acttab_insert() call
** also resets the aLookahead[] array in preparation for the next
** state number.
*/
#[derive(Debug, Copy, Clone)]
struct LookaheadAction {
    lookahead: usize, // Value of the lookahead token
    action: usize,    // Action to take on the given lookahead
}

#[derive(Debug)]
struct ActionSet {
    a_lookahead: Vec<LookaheadAction>, // A single new transaction set
}

impl ActionSet {
    fn new() -> ActionSet {
        ActionSet {
            a_lookahead: Vec::new(),
        }
    }
    /* Add a new action to the current transaction set.
     **
     ** This routine is called once for each lookahead for a particular
     ** state.
     */
    fn add_action(&mut self, lookahead: usize, action: usize) {
        self.a_lookahead.push(LookaheadAction { lookahead, action });
    }
}

#[derive(Debug)]
struct ActTab {
    a_action: Vec<Option<LookaheadAction>>, // The yy_action[] table under construction
}

impl ActTab {
    fn new() -> ActTab {
        ActTab {
            a_action: Vec::new(),
        }
    }
    /*
     ** Add the transaction set built up with prior calls to add_action()
     ** into the current action table.  Then reset the transaction set back
     ** to an empty set in preparation for a new round of add_action() calls.
     **
     ** Return the offset into the action table of the new transaction.
     */
    fn insert_action_set(&mut self, at2: &ActionSet) -> i32 {
        assert!(!at2.a_lookahead.is_empty());

        //at2.a_lookahead is sorted by lookahead
        let min_lookahead = at2.a_lookahead.first().unwrap().lookahead;
        let min_action = at2.a_lookahead.first().unwrap().action;
        let max_lookahead = at2.a_lookahead.last().unwrap().lookahead;

        /* Scan the existing action table looking for an offset that is a
         ** duplicate of the current transaction set.  Fall out of the loop
         ** if and when the duplicate is found.
         **
         ** i is the index in self.a_action[] where min_lookahead is inserted.
         */
        let mut found = None;
        'la: for (i, a) in self.a_action.iter().enumerate().rev() {
            let a = match a {
                None => continue,
                Some(a) => a,
            };
            /* All lookaheads and actions in the a_lookahead[] transaction
             ** must match against the candidate a_action[i] entry. */
            if a.lookahead != min_lookahead {
                continue;
            }
            if a.action != min_action {
                continue;
            }

            for jla in &at2.a_lookahead {
                let k = jla.lookahead as i32 - min_lookahead as i32 + i as i32;
                if k < 0 || k as usize >= self.a_action.len() {
                    continue 'la;
                }
                match self.a_action[k as usize] {
                    Some(ka) => {
                        if jla.lookahead != ka.lookahead {
                            continue 'la;
                        }
                        if jla.action != ka.action {
                            continue 'la;
                        }
                    }
                    None => continue 'la,
                }
            }

            /* No possible lookahead value that is not in the aLookahead[]
             ** transaction is allowed to match aAction[i] */
            let mut n = 0;
            for (j, ja) in self.a_action.iter().enumerate() {
                let ja = match ja {
                    None => continue,
                    Some(ja) => ja,
                };
                if ja.lookahead as i32 == (j as i32 + min_lookahead as i32 - i as i32) {
                    n += 1;
                }
            }
            if n == at2.a_lookahead.len() {
                found = Some(i);
                break; /* An exact match is found at offset i */
            }
        }
        /* If no existing offsets exactly match the current transaction, find an
         ** an empty offset in the aAction[] table in which we can add the
         ** aLookahead[] transaction.
         */
        let i = match found {
            None => {
                /* Look for holes in the aAction[] table that fit the current
                 ** aLookahead[] transaction.  Leave i set to the offset of the hole.
                 ** If no holes are found, i is left at self.n_action, which means the
                 ** transaction will be appended. */
                let mut r = self.a_action.len();
                'ia: for i in 0..self.a_action.len() + max_lookahead {
                    for jla in &at2.a_lookahead {
                        let k = jla.lookahead - min_lookahead + i;
                        if let Some(Some(_)) = self.a_action.get(k) {
                            continue 'ia;
                        }
                    }
                    for (j, ja) in self.a_action.iter().enumerate() {
                        let ja = match ja {
                            None => continue,
                            Some(ja) => ja.lookahead as i32,
                        };
                        if ja == (j as i32 + min_lookahead as i32 - i as i32) {
                            continue 'ia;
                        }
                    }
                    r = i;
                    //println!("hole at {}", i);
                    break;
                }
                r
            }
            Some(i) => {
                //println!("matched at {}", i);
                i
            }
        };

        let res = i as i32 - min_lookahead as i32;

        /* Insert transaction set at index i. */
        for jla in &at2.a_lookahead {
            let k = (jla.lookahead as i32 + res) as usize;
            if k >= self.a_action.len() {
                self.a_action.resize(k + 1, None);
            }
            self.a_action[k] = Some(*jla);
        }

        /*
        print!("LK:");
        for jla in &at2.a_lookahead {
            print!(" {:>2}/{:<2}", jla.action, jla.lookahead);
        }
        print!(" -> {}", res);

        print!("AC:");
        for (j, ja) in self.a_action.iter().enumerate() {
            match ja {
                None => {
                    print!(" {}:-----", j);
                }
                Some(ja) => {
                    print!(" {}:{:>2}/{:<2}", j, ja.action, ja.lookahead);
                }
            }
        }
        println!();
        println!();
        */

        /* Return the offset that is added to the lookahead in order to get the
         ** index into yy_action of the action */
        res
    }
}

fn minimum_signed_type(max: usize) -> Ident {
    if max < 0x80 {
        parse_quote!(i8)
    } else if max < 0x8000 {
        parse_quote!(i16)
    } else {
        parse_quote!(i32)
    }
}

fn minimum_unsigned_type(max: usize) -> Ident {
    if max < 0x100 {
        parse_quote!(u8)
    } else if max < 0x10000 {
        parse_quote!(u16)
    } else {
        parse_quote!(u32)
    }
}

fn error<T, M: Display>(msg: M) -> syn::Result<T> {
    Err(syn::Error::new(Span::call_site(), msg))
}

fn error_span<T>(span: Span, msg: &'static str) -> syn::Result<T> {
    Err(syn::Error::new(span, msg))
}

fn is_terminal_ident(id: &Ident) -> bool {
    id.to_string().chars().next().unwrap().is_ascii_uppercase()
}

fn is_nonterminal_ident(id: &Ident) -> bool {
    id.to_string().chars().next().unwrap().is_ascii_lowercase()
}

impl Pomelo {
    pub fn new_from_decls(decls: Vec<Decl>) -> syn::Result<Pomelo> {
        let mut pomelo = Pomelo {
            the_symbols: VecRef::new(),
            the_states: VecRef::new(),
            the_rules: VecRef::new(),
            the_configs: VecRef::new(),
            module: parse_quote!(parser),
            includes: Vec::new(),
            syntax_error: None,
            parse_fail: None,
            stack_overflow: None,
            token_enum: None,
            parser_struct: None,
            states: Vec::new(),
            rules: Vec::new(),
            default_index: 0,
            num_terminals: 0,
            symbols: Vec::new(),
            error_symbol: SymbolId::dangling(), //temporary fake value
            wildcard: None,
            arg: None,
            err_type: None,
            nconflict: 0,
            has_fallback: false,
            default_type: None,
            start: None,
            optional_tokens: HashMap::new(),
            extra_token: None,
            stack_type: None,
            stack_limit: 100,
            verbose: false,
        };

        pomelo.symbol_new("$", NewSymbolType::Terminal);
        pomelo.error_symbol = pomelo.symbol_new("error", NewSymbolType::NonTerminal);

        let mut pdata = ParserData { precedence: 0 };

        for decl in decls {
            pomelo.parse_one_decl(&mut pdata, decl)?;
        }

        pomelo.symbol_new("{default}", NewSymbolType::NonTerminal);

        if pomelo.rules.is_empty() {
            return error("Grammar must have some rules"); //tested
        }

        Ok(pomelo)
    }
    pub fn module_name(&self) -> &Ident {
        &self.module
    }
    pub fn build(&mut self) -> syn::Result<TokenStream> {
        self.prepare();
        self.find_rule_precedences();
        self.normalize_rules()?;
        self.find_first_sets();
        self.find_states()?;
        self.find_links();
        self.find_follow_sets();
        self.find_actions()?;

        if self.verbose || self.nconflict > 0 {
            let report = self.report_output();
            if self.nconflict > 0 {
                return error(format!("Parsing conflicts:\n {}", report));
            }
            println!("{}", report);
        }

        self.compress_tables();
        self.resort_states();
        let src = self.generate_source()?;
        //println!("default_index={}, num_terminals={}", self.default_index, self.num_terminals);
        Ok(src)
    }

    fn prepare(&mut self) {
        //First there are all the Terminals, the first one is $
        //Then the NonTerminals, the last one is {default}
        //And finally the MultiTerminals
        //Do not impl Ord, because that requires Eq, that we do not need.
        //
        //We have to take 'symbols' out of self to be able to borrow self in the callback.
        let mut symbols = std::mem::take(&mut self.symbols);
        symbols.sort_by(|a, b| {
            fn symbol_ord(s: &SymbolType) -> i32 {
                match s {
                    Terminal => 0,
                    NonTerminal { .. } => 1,
                    MultiTerminal(_) => 2,
                }
            }
            let a = symbol_ord(&self.the_symbols.get(a).typ);
            let b = symbol_ord(&self.the_symbols.get(b).typ);
            a.cmp(&b)
        });

        let mut last_terminal = 0;
        let mut default_index = 0;
        for (i, s) in symbols.iter().enumerate() {
            self.the_symbols.get_mut(s).index = i;
            match self.the_symbols.get(s).typ {
                Terminal => last_terminal = i,
                NonTerminal { .. } => default_index = i,
                _ => (),
            }
        }

        self.symbols = symbols;
        self.num_terminals = last_terminal + 1;
        self.default_index = default_index;

        //Default start symbol is the LHS of the first rule
        if self.start.is_none() {
            let start = self.the_rules.get(self.rules.first().unwrap()).lhs.0;
            self.start = Some(start);
        }
        if let Some(extra_token) = &self.extra_token {
            for i in 1..self.num_terminals {
                let mut s = self.the_symbols.get_mut(self.symbols[i]);
                s.data_type = match s.data_type.take() {
                    None => Some(extra_token.clone()),
                    Some(dt) => Some(parse_quote!((#extra_token, #dt))),
                }
            }
        }

        //For every optional token T of type ty (a new non-terminal _t of type Option<ty> has already been created),
        //add two new rules:
        //  _n ::= T { None }
        //  _n ::= T(_A) { Some(_A) }
        //We consume the optional_tokens map, it is no longer needed
        let optional_tokens = std::mem::take(&mut self.optional_tokens);
        for (sym_r, SymbolSpan(sym_l, span)) in optional_tokens {
            let dt = self
                .the_symbols
                .get(sym_r)
                .data_type
                .clone()
                .unwrap_or_else(|| parse_quote!(()));
            self.the_symbols.get_mut(sym_l).data_type = Some(parse_quote!(Option<#dt>));
            let sym_l = SymbolSpan(sym_l, span);

            self.create_rule(
                span,
                sym_l.clone(),
                vec![],
                Some(parse_quote!({ None })),
                None,
            );

            let rhs = SymbolAlias(sym_r, span, Some(parse_quote!(_A)));
            self.create_rule(
                span,
                sym_l,
                vec![rhs],
                Some(parse_quote!({ Some(_A) })),
                None,
            );
        }
    }

    /* Find a precedence symbol of every rule in the grammar.
     **
     ** Those rules which have a precedence symbol coded in the input
     ** grammar using the "[symbol]" construct will already have the
     ** rp->precsym field filled.  Other rules take as their precedence
     ** symbol the first RHS symbol with a defined precedence.  If there
     ** are not RHS symbols with a defined precedence, the precedence
     ** symbol field is left blank.
     */
    fn find_rule_precedences(&mut self) {
        for rp in &self.rules {
            let mut rp = self.the_rules.get_mut(rp);
            if let Some(ps) = &rp.prec_sym {
                rp.precedence = self.the_symbols.get(ps).precedence;
                continue;
            }
            for SymbolAlias(sp, ..) in &rp.rhs {
                let b = self.the_symbols.get(sp);
                match &b.typ {
                    MultiTerminal(sub_sym) => {
                        if let Some(prec) = sub_sym
                            .iter()
                            .find_map(|msp| self.the_symbols.get(msp).precedence)
                        {
                            rp.prec_sym = Some(*sp);
                            rp.precedence = Some(prec);
                            break;
                        }
                    }
                    _ if b.precedence.is_some() => {
                        rp.prec_sym = Some(*sp);
                        rp.precedence = b.precedence;
                        break;
                    }
                    _ => {}
                }
            }
        }
    }

    //If a rule has a typed LHS but not code, it will fail to compile, because the LHS must
    //be assigned. Before issuing an error, we'll try to auto-fix it if the following is
    //true:
    // * no alias on the RHS
    // * only one symbol in the RHS has type
    // * the type of that symbol is the same as the type of the RHS
    fn normalize_rules(&mut self) -> syn::Result<()> {
        for rp in &self.rules {
            let mut rp = self.the_rules.get_mut(rp);
            if self.the_symbols.get(rp.lhs.0).data_type.is_some() && rp.code.is_none() {
                if rp.rhs.iter().all(|SymbolAlias(_, _, a)| a.is_none()) {
                    let mut rtyped = rp
                        .rhs
                        .iter_mut()
                        .filter(|SymbolAlias(symbol, _, _)| {
                            self.the_symbols.get(symbol).data_type.is_some()
                        })
                        .collect::<Vec<_>>();
                    if let [SymbolAlias(_, _, alias)] = &mut rtyped[..] {
                        *alias = Some(parse_quote!(_A));
                        rp.code = Some(parse_quote!({ _A }));
                        continue;
                    }
                }
                return error_span(
                    rp.lhs.1,
                    "This rule has a typed LHS but no code to assign it",
                ); //tested
            }
        }
        Ok(())
    }

    /* Find all nonterminals which will generate the empty string.
     ** Then go back and compute the first sets of every nonterminal.
     ** The first set is the set of all terminal symbols which can begin
     ** a string generated by that nonterminal.
     */
    fn find_first_sets(&mut self) {
        loop {
            let mut progress = false;
            for rp in &self.rules {
                let rp = self.the_rules.get(rp);
                let lhs = rp.lhs.0;
                if self.the_symbols.get(lhs).is_lambda() {
                    continue;
                }

                let mut all_lambda = true;
                for SymbolAlias(sp, ..) in &rp.rhs {
                    let sp = self.the_symbols.get(sp);
                    if !sp.is_lambda() {
                        all_lambda = false;
                        break;
                    }
                }
                if all_lambda {
                    if let NonTerminal { lambda, .. } = &mut self.the_symbols.get_mut(lhs).typ {
                        *lambda = true;
                        progress = true;
                    } else {
                        unreachable!("Only NonTerminals have lambda");
                    }
                }
            }
            if !progress {
                break;
            }
        }
        //Now compute all first sets
        loop {
            let mut progress = false;

            for rp in &self.rules {
                let rp = self.the_rules.get(rp);
                let s1 = &rp.lhs.0;
                for SymbolAlias(s2, ..) in &rp.rhs {
                    //First check if s1 and s2 are the same, or else s1.borrow_mut() will panic
                    if s1 == s2 {
                        if !self.the_symbols.get(s1).is_lambda() {
                            break;
                        }
                        continue;
                    }
                    let b2 = self.the_symbols.get(s2);
                    if let NonTerminal {
                        first_set: s1_first_set,
                        ..
                    } = &mut self.the_symbols.get_mut(s1).typ
                    {
                        match &b2.typ {
                            Terminal => {
                                progress |= s1_first_set.insert(b2.index);
                                break;
                            }
                            MultiTerminal(sub_sym) => {
                                for ss in sub_sym {
                                    progress |= s1_first_set.insert(self.the_symbols.get(ss).index);
                                }
                                break;
                            }
                            NonTerminal {
                                first_set: s2_first_set,
                                lambda: b2_lambda,
                                ..
                            } => {
                                let n1 = s1_first_set.len();
                                s1_first_set.extend(s2_first_set);
                                progress |= s1_first_set.len() > n1;
                                if !b2_lambda {
                                    break;
                                }
                            }
                        }
                    }
                }
            }
            if !progress {
                break;
            }
        }
    }

    /* Compute all LR(0) states for the grammar.  Links
     ** are added to between some states so that the LR(1) follow sets
     ** can be computed later.
     */
    fn find_states(&mut self) -> syn::Result<()> {
        /* Find the start symbol */
        let sp = self.start.as_ref().unwrap();

        /* Make sure the start symbol doesn't occur on the right-hand side of
         ** any rule.  Report an error if it does.  (YACC would generate a new
         ** start symbol in this case.) */
        for rp in &self.rules {
            let rp = self.the_rules.get_mut(rp);
            for SymbolAlias(r, span, ..) in &rp.rhs {
                if sp == r {
                    return error_span(*span, "start symbol on the RHS of a rule");
                    //tested
                }
            }
        }

        let mut basis = Vec::new();

        /* The basis configuration set for the first state
         ** is all rules which have the start symbol as their
         ** left-hand side */
        let rules = self
            .the_symbols
            .get(sp)
            .get_non_terminal_rules()
            .map(|s| s.to_owned());
        if let Some(rules) = rules {
            for rp in rules {
                self.the_rules.get_mut(rp).lhs_start = true;

                let cfg = self.add_config(&mut basis, rp, 0);
                self.the_configs.get_mut(cfg).fws.insert(0);
            }
        }
        self.get_state(basis.clone(), basis)?;

        Ok(())
    }

    /* Compute the first state.  All other states will be
     ** computed automatically during the computation of the first one.
     ** The returned pointer to the first state is not used. */
    fn get_state(&mut self, mut bp: Vec<ConfigId>, cur: Vec<ConfigId>) -> syn::Result<StateId> {
        bp.sort_by(|a, b| config_cmp(self, *a, *b));
        /* Get a state with the same basis */
        match self.state_find(&bp) {
            Some(stp) => {
                /* A state with the same basis already exists!  Copy all the follow-set
                 ** propagation links from the state under construction into the
                 ** preexisting state, then return a pointer to the preexisting state */
                let bstp = self.the_states.get(stp);
                for (x, y) in bp.into_iter().zip(&bstp.basis) {
                    let mut y = self.the_configs.get_mut(y);
                    y.bplp.extend(&self.the_configs.get(x).bplp);
                }
                Ok(stp)
            }
            None => {
                /* This really is a new state. Construct all the details */
                let mut configs = self.configlist_closure(cur)?;
                configs.sort_by(|a, b| config_cmp(self, *a, *b));
                let stp = State {
                    configs,
                    basis: bp.clone(),
                    state_num: self.states.len(),
                    actions: Vec::new(),
                    n_tkn_act: 0,
                    n_nt_act: 0,
                    i_tkn_ofst: None,
                    i_nt_ofst: None,
                    i_dflt: 0,
                };
                let id = self.the_states.push(stp);
                self.states.push(id);
                self.build_shifts(id)?;
                Ok(id)
            }
        }
    }
    /* Construct all successor states to the given state.  A "successor"
     ** state is any state which can be reached by a shift action.
     */
    fn build_shifts(&mut self, state: StateId) -> syn::Result<()> {
        /* Each configuration becomes complete after it contibutes to a successor
         ** state.  Initially, all configurations are incomplete */

        for cfp in &self.the_states.get(state).configs {
            self.the_configs.get_mut(cfp).status = CfgStatus::Incomplete;
        }
        let mut aps = Vec::new();
        /* Loop through all configurations of the state "stp" */
        let configs = self.the_states.get(state).configs.clone();
        for (icfp, cfp) in configs.iter().enumerate() {
            let cfp = self.the_configs.get(cfp);
            if let CfgStatus::Complete = cfp.status {
                continue;
            } /* Already used by inner loop */
            if cfp.dot >= self.the_rules.get(cfp.rule).rhs.len() {
                continue;
            } /* Can't shift this config */
            let SymbolAlias(sp, ..) = self.the_rules.get(cfp.rule).rhs[cfp.dot]; /* Symbol after the dot */
            let mut basis = Vec::new();
            drop(cfp);

            /* For every configuration in the state "stp" which has the symbol "sp"
             ** following its dot, add the same configuration to the basis set under
             ** construction but with the dot shifted one symbol to the right. */
            let state_configs = self.the_states.get(state).configs[icfp..].to_owned();
            for bcfp_ in state_configs {
                let rule;
                let dot;
                {
                    let bcfp = self.the_configs.get(bcfp_);
                    if let CfgStatus::Complete = bcfp.status {
                        continue;
                    } /* Already used */
                    if bcfp.dot >= self.the_rules.get(bcfp.rule).rhs.len() {
                        continue;
                    } /* Can't shift this one */
                    let SymbolAlias(bsp, ..) = self.the_rules.get(bcfp.rule).rhs[bcfp.dot]; /* Get symbol after dot */
                    if bsp != sp {
                        continue;
                    } /* Must be same as for "cfp" */
                    rule = bcfp.rule;
                    dot = bcfp.dot + 1;
                }
                let newcfg = self.add_config(&mut basis, rule, dot);

                self.the_configs.get_mut(bcfp_).status = CfgStatus::Complete; /* Mark this config as used */
                self.the_configs.get_mut(newcfg).bplp.push(bcfp_);
            }

            /* Get a pointer to the state described by the basis configuration set
             ** constructed in the preceding loop */
            let newstp = self.get_state(basis.clone(), basis)?;

            /* The state "newstp" is reached from the state "stp" by a shift action
             ** on the symbol "sp" */
            let bsp = self.the_symbols.get(sp);
            match &bsp.typ {
                MultiTerminal(sub_sym) => {
                    for ss in sub_sym {
                        let detail = ActionDetail::Shift(newstp);
                        aps.push(RefCell::new(Action {
                            look_ahead: *ss,
                            detail,
                        }));
                    }
                }
                _ => {
                    let detail = ActionDetail::Shift(newstp);
                    aps.push(RefCell::new(Action {
                        look_ahead: sp,
                        detail,
                    }));
                }
            }
        }
        self.the_states.get_mut(state).actions.extend(aps);

        Ok(())
    }

    /** Construct the propagation links */
    fn find_links(&mut self) {
        /* Housekeeping detail:
         ** Add to every propagate link a pointer back to the state to
         ** which the link is attached. */
        //for stp in &self.states {
        //    for cfp in &stp.borrow().cfp {
        //        cfp.borrow_mut().stp = Some(stp.into());
        //    }
        //}

        /* Convert all backlinks into forward links.  Only the forward
         ** links are used in the follow-set computation. */
        for stp in &self.states {
            for cfp in &self.the_states.get(stp).configs {
                for plp in &self.the_configs.get(cfp).bplp {
                    self.the_configs.get_mut(plp).fplp.push(*cfp);
                }
            }
        }
    }

    /* Compute all followsets.
     **
     ** A followset is the set of all symbols which can come immediately
     ** after a configuration.
     */
    fn find_follow_sets(&mut self) {
        for stp in &self.states {
            for cfp in &self.the_states.get(stp).configs {
                self.the_configs.get_mut(cfp).status = CfgStatus::Incomplete;
            }
        }

        let mut progress = true;
        while progress {
            progress = false;
            for stp in &self.states {
                for cfp in &self.the_states.get(stp).configs {
                    let (fws, fplp) = {
                        let cfp = self.the_configs.get(cfp);
                        if let CfgStatus::Complete = cfp.status {
                            continue;
                        }
                        (cfp.fws.clone(), cfp.fplp.clone())
                    };
                    for plp in &fplp {
                        let mut plp = self.the_configs.get_mut(plp);
                        let n = plp.fws.len();
                        plp.fws.extend(&fws);
                        if plp.fws.len() > n {
                            plp.status = CfgStatus::Incomplete;
                            progress = true;
                        }
                    }
                    self.the_configs.get_mut(cfp).status = CfgStatus::Complete;
                }
            }
        }
    }

    /* Compute the reduce actions, and resolve conflicts.
     */
    fn find_actions(&mut self) -> syn::Result<()> {
        /* Add all of the reduce actions
         ** A reduce action is added for each element of the followset of
         ** a configuration which has its dot at the extreme right.
         */
        for stp in &self.states {
            let mut aps = Vec::new();
            let mut stp = self.the_states.get_mut(stp);
            for cfp in &stp.configs {
                let cfp = self.the_configs.get(cfp);
                if cfp.dot == self.the_rules.get(cfp.rule).rhs.len() {
                    /* Is dot at extreme right? */
                    for j in 0..self.num_terminals {
                        if cfp.fws.contains(&j) {
                            /* Add a reduce action to the state "stp" which will reduce by the
                             ** rule "cfp->rp" if the lookahead symbol is "lemp->symbols[j]" */
                            let detail = ActionDetail::Reduce(cfp.rule);
                            aps.push(RefCell::new(Action {
                                look_ahead: self.symbols[j],
                                detail,
                            }));
                        }
                    }
                }
            }
            stp.actions.extend(aps);
        }

        /* Add the accepting token */
        let sp = self.start.unwrap();

        /* Add to the first state (which is always the starting state of the
         ** finite state machine) an action to ACCEPT if the lookahead is the
         ** start nonterminal.  */
        self.the_states
            .get_mut(self.states.first().unwrap())
            .actions
            .push(RefCell::new(Action {
                look_ahead: sp,
                detail: ActionDetail::Accept,
            }));

        /* Resolve conflicts */
        let mut nconflict = 0;
        for stp in &self.states {
            self.the_states.get_mut(stp).actions.sort_by(|a, b| {
                action_cmp(&self.the_symbols, &self.the_states, &self.the_rules, a, b)
            });
            let stp = self.the_states.get(stp);
            let len = stp.actions.len();
            for i in 0..len {
                let ap = &stp.actions[i];
                for j in i + 1..len {
                    let nap = &stp.actions[j];
                    if ap.borrow().look_ahead == nap.borrow().look_ahead {
                        /* The two actions "ap" and "nap" have the same lookahead.
                         ** Figure out which one should be used */
                        nconflict +=
                            if self.resolve_conflict(&mut ap.borrow_mut(), &mut nap.borrow_mut()) {
                                1
                            } else {
                                0
                            };
                    } else {
                        break;
                    }
                }
            }
        }
        self.nconflict += nconflict;

        /* Report an error for each rule that can never be reduced. */
        for stp in &self.states {
            for a in &self.the_states.get(stp).actions {
                let a = a.borrow();
                if let ActionDetail::Reduce(x) = &a.detail {
                    self.the_rules.get_mut(x).can_reduce = true;
                }
            }
        }
        for rp in &self.rules {
            let rp = self.the_rules.get(rp);
            if !rp.can_reduce {
                return error_span(rp.span, "This rule cannot be reduced"); //tested
            }
        }
        Ok(())
    }

    /* Resolve a conflict between the two given actions.  If the
     ** conflict can't be resolved, return non-zero.
     **
     ** NO LONGER TRUE:
     **   To resolve a conflict, first look to see if either action
     **   is on an error rule.  In that case, take the action which
     **   is not associated with the error rule.  If neither or both
     **   actions are associated with an error rule, then try to
     **   use precedence to resolve the conflict.
     **
     ** If either action is a SHIFT, then it must be apx.  This
     ** function won't work if apx->type==REDUCE and apy->type==SHIFT.
     */
    fn resolve_conflict(&self, apx: &mut Action, apy: &mut Action) -> bool {
        use ActionDetail::*;
        let (err, ax, ay) = match (apx.detail.clone(), apy.detail.clone()) {
            (Shift(x), Shift(y)) => (true, Shift(x), SSConflict(y)),
            /* Use operator associativity to break tie */
            (Shift(x), Reduce(y)) => {
                let precx = self.the_symbols.get(apx.look_ahead).precedence;
                let precy = self.the_rules.get(y).precedence;

                match (precx, precy) {
                    (Some(px), Some(py)) => match precedence_cmp(px, py) {
                        Ordering::Less => (false, SHResolved(x), Reduce(y)),
                        Ordering::Equal => (false, Error, Reduce(y)),
                        Ordering::Greater => (false, Shift(x), RDResolved(y)),
                    },
                    _ => (true, Shift(x), SRConflict(y)),
                }
            }
            (Reduce(x), Reduce(y)) => {
                let precx = self.the_rules.get(x).precedence;
                let precy = self.the_rules.get(y).precedence;

                match (precx, precy) {
                    (Some(px), Some(py)) => match precedence_cmp(px, py) {
                        Ordering::Less => (false, RDResolved(x), Reduce(y)),
                        Ordering::Equal => (true, Reduce(x), RRConflict(y)),
                        Ordering::Greater => (false, Reduce(x), RDResolved(y)),
                    },
                    _ => (true, Reduce(x), RRConflict(y)),
                }
            }
            /* The REDUCE/SHIFT case cannot happen because SHIFTs come before
             ** REDUCEs on the list.  If we reach this point it must be because
             ** the parser conflict had already been resolved. */
            _ => return false,
        };
        apx.detail = ax;
        apy.detail = ay;
        err
    }

    /* Reduce the size of the action tables, if possible, by making use
     ** of defaults.
     **
     ** In this version, we take the most frequent REDUCE action and make
     ** it the default.  Except, there is no default if the wildcard token
     ** is a possible look-ahead.
     */
    fn compress_tables(&mut self) {
        use ActionDetail::*;

        let def_symbol = self.symbol_find("{default}").unwrap();

        for stp in &self.states {
            {
                let mut nbest = 0;
                let mut rbest = None;
                let mut uses_wildcard = false;
                let stp = self.the_states.get(stp);
                for (iap, ap) in stp.actions.iter().enumerate() {
                    let ap = ap.borrow();
                    match (&ap.detail, &self.wildcard) {
                        (Shift(_), Some(w)) => {
                            if ap.look_ahead == *w {
                                uses_wildcard = true;
                            }
                        }
                        (Reduce(rp), _) => {
                            if self.the_rules.get(rp).lhs_start {
                                continue;
                            }
                            if rbest.as_ref() == Some(rp) {
                                continue;
                            }
                            let mut n = 1;
                            for ap2 in &stp.actions[iap + 1..] {
                                let ap2 = ap2.borrow();
                                match &ap2.detail {
                                    Reduce(rp2) => {
                                        if rbest.as_ref() == Some(rp2) {
                                            continue;
                                        }
                                        if rp2 == rp {
                                            n += 1;
                                        }
                                    }
                                    _ => continue,
                                }
                            }
                            if n > nbest {
                                nbest = n;
                                rbest = Some(*rp);
                            }
                        }
                        _ => continue,
                    }
                }

                /* Do not make a default if the number of rules to default
                 ** is not at least 1 or if the wildcard token is a possible
                 ** lookahead.
                 */
                if nbest < 1 || uses_wildcard {
                    continue;
                }
                let rbest = rbest.unwrap();

                /* Combine matching REDUCE actions into a single default */

                let mut apbest = None;
                for (iap, ap) in stp.actions.iter().enumerate() {
                    let bap = ap.borrow();
                    if let Reduce(rp) = &bap.detail {
                        if *rp == rbest {
                            apbest = Some((iap, ap));
                            break;
                        }
                    }
                }
                if let Some((iap, ap)) = apbest {
                    ap.borrow_mut().look_ahead = def_symbol;
                    for ap2 in &stp.actions[iap + 1..] {
                        let mut ap2 = ap2.borrow_mut();
                        let unuse = match &ap2.detail {
                            Reduce(rp) => *rp == rbest,
                            _ => false,
                        };
                        if unuse {
                            ap2.detail = NotUsed;
                        }
                    }
                }
            }
            self.the_states.get_mut(stp).actions.sort_by(|a, b| {
                action_cmp(&self.the_symbols, &self.the_states, &self.the_rules, a, b)
            });
        }
    }

    /*
     ** Renumber and resort states so that states with fewer choices
     ** occur at the end.  Except, keep state 0 as the first state.
     */
    fn resort_states(&mut self) {
        for stp in &self.states {
            let mut n_tkn_act = 0;
            let mut n_nt_act = 0;
            let mut i_dflt = self.states.len() + self.rules.len();

            for ap in &self.the_states.get(stp).actions {
                let ap = ap.borrow();
                if let Some(x) = self.compute_action(&ap) {
                    let index = self.the_symbols.get(ap.look_ahead).index;
                    if index < self.num_terminals {
                        n_tkn_act += 1;
                    } else if index < self.default_index {
                        n_nt_act += 1;
                    } else {
                        i_dflt = x;
                    }
                }
            }

            let mut stp = self.the_states.get_mut(stp);
            stp.n_tkn_act = n_tkn_act;
            stp.n_nt_act = n_nt_act;
            stp.i_dflt = i_dflt;
        }
        //Take states out of self to be able to use `self`
        let mut states = std::mem::take(&mut self.states);
        states[1..].sort_by(|a, b| self.state_resort_cmp(*a, *b));
        for (i, stp) in states.iter().enumerate() {
            self.the_states.get_mut(stp).state_num = i;
        }
        self.states = states;
    }

    /* Given an action, compute the integer value for that action
     ** which is to be put in the action table of the generated machine.
     ** Return None if no action should be generated.
     */
    fn compute_action(&self, ap: &Action) -> Option<usize> {
        use ActionDetail::*;
        let act = match &ap.detail {
            Shift(stp) => self.the_states.get(stp).state_num,
            Reduce(rp) => self.the_rules.get(rp).index + self.states.len(),
            Error => self.states.len() + self.rules.len(),
            Accept => self.states.len() + self.rules.len() + 1,
            _ => return None,
        };
        Some(act)
    }

    fn report_output(&self) -> String {
        let mut state_info = String::new();
        for stp in &self.states {
            let stp = self.the_states.get(stp);
            writeln!(state_info, "State {}:", stp.state_num).unwrap();
            for cfp in &stp.configs {
                let cfp = self.the_configs.get(cfp);
                let rule = self.the_rules.get(cfp.rule);
                if cfp.dot == rule.rhs.len() {
                    write!(state_info, "    {:>5} ", format!("({})", rule.index)).unwrap();
                } else {
                    write!(state_info, "          ").unwrap();
                }
                write!(state_info, "{} ::=", self.the_symbols.get(rule.lhs.0).name).unwrap();
                for (i, SymbolAlias(sp, ..)) in rule.rhs.iter().enumerate() {
                    if i == cfp.dot {
                        write!(state_info, " *").unwrap();
                    }
                    let sp = self.the_symbols.get(sp);
                    if let MultiTerminal(sub_sym) = &sp.typ {
                        for (j, ss) in sub_sym.iter().enumerate() {
                            let ss = self.the_symbols.get(ss);
                            if j == 0 {
                                write!(state_info, " {}", ss.name).unwrap();
                            } else {
                                write!(state_info, "|{}", ss.name).unwrap();
                            }
                        }
                    } else {
                        write!(state_info, " {}", sp.name).unwrap();
                    }
                }
                if cfp.dot == rule.rhs.len() {
                    write!(state_info, " *").unwrap();
                }
                writeln!(state_info).unwrap();
            }
            writeln!(state_info).unwrap();
            for ap in &stp.actions {
                let ap = ap.borrow();
                use ActionDetail::*;
                let sp = self.the_symbols.get(ap.look_ahead);
                match &ap.detail {
                    Shift(stp) => {
                        write!(
                            state_info,
                            "{:>30} shift  {}",
                            sp.name,
                            self.the_states.get(stp).state_num
                        )
                        .unwrap();
                    }
                    Reduce(rp) => {
                        write!(
                            state_info,
                            "{:>30} reduce {}",
                            sp.name,
                            self.the_rules.get(rp).index
                        )
                        .unwrap();
                    }
                    Accept => {
                        write!(state_info, "{:>30} accept", sp.name).unwrap();
                    }
                    Error => {
                        write!(state_info, "{:>30} error", sp.name).unwrap();
                    }
                    SRConflict(rp) | RRConflict(rp) => {
                        write!(
                            state_info,
                            "{:>30} reduce {:<3} ** Parsing conflict **",
                            sp.name,
                            self.the_rules.get(rp).index
                        )
                        .unwrap();
                    }
                    SSConflict(stp) => {
                        write!(
                            state_info,
                            "{:>30} shift  {:<3} ** Parsing conflict **",
                            sp.name,
                            self.the_states.get(stp).state_num
                        )
                        .unwrap();
                    }
                    SHResolved(stp) => {
                        write!(
                            state_info,
                            "{:>30} shift  {:<3} -- dropped by precedence",
                            sp.name,
                            self.the_states.get(stp).state_num
                        )
                        .unwrap();
                    }
                    RDResolved(rp) => {
                        write!(
                            state_info,
                            "{:>30} reduce {:<3} -- dropped by precedence",
                            sp.name,
                            self.the_rules.get(rp).index
                        )
                        .unwrap();
                    }
                    _ => continue,
                }
                writeln!(state_info).unwrap();
            }
            writeln!(state_info).unwrap();
        }
        if self.verbose {
            writeln!(
                state_info,
                "----------------------------------------------------"
            )
            .unwrap();
            writeln!(state_info, "Symbols:").unwrap();
            for (i, sp) in self.symbols.iter().enumerate() {
                let sp = self.the_symbols.get(sp);
                write!(state_info, "  {:3}: {}", i, sp.name).unwrap();
                /*
                   if let NonTerminal{first_set, lambda, ..} = &sp.typ {
                   print!(":");
                   if *lambda {
                   print!(" <lambda>");
                   }
                   for j in 0 .. self.num_terminals {
                   if first_set.contains(&j) {
                   print!("={}", self.symbols[j].borrow().name);
                   }
                   }
                   }
                */
                writeln!(state_info).unwrap();
            }
        }
        state_info
    }

    fn state_find(&mut self, bp: &[ConfigId]) -> Option<StateId> {
        let res = self.states.iter().find(|s| {
            let sbp = &self.the_states.get(*s).basis;
            if sbp.len() != bp.len() {
                return false;
            }
            for (a, b) in sbp.iter().zip(bp) {
                let a = self.the_configs.get(a);
                let b = self.the_configs.get(b);
                if a.rule != b.rule || a.dot != b.dot {
                    return false;
                }
            }
            true
        });
        res.cloned()
    }

    /* Compute the closure of the configuration list */
    fn configlist_closure(&mut self, mut cur: Vec<ConfigId>) -> syn::Result<Vec<ConfigId>> {
        let mut i = 0;
        while i < cur.len() {
            //println!("I = {} < {}", i, cur.len());
            let cfp = cur[i];
            let rhs = self
                .the_rules
                .get(self.the_configs.get(cfp).rule)
                .rhs
                .clone();
            let dot = self.the_configs.get(cfp).dot;
            if dot < rhs.len() {
                let SymbolAlias(sp, span, ..) = &rhs[dot];
                let rules = self
                    .the_symbols
                    .get(sp)
                    .get_non_terminal_rules()
                    .map(|s| s.to_owned());
                if let Some(rules) = rules {
                    if rules.is_empty() && *sp != self.error_symbol {
                        return error_span(*span, "Nonterminal has no rules"); //tested
                    }
                    for newrp in rules {
                        let newcfp = self.add_config(&mut cur, newrp, 0);
                        let mut broken = false;
                        for SymbolAlias(xsp, ..) in &rhs[dot + 1..] {
                            let xsp = self.the_symbols.get(xsp);
                            match &xsp.typ {
                                Terminal => {
                                    let mut newcfp = self.the_configs.get_mut(newcfp);
                                    newcfp.fws.insert(xsp.index);
                                    broken = true;
                                    break;
                                }
                                MultiTerminal(sub_sym) => {
                                    let mut newcfp = self.the_configs.get_mut(newcfp);
                                    for k in sub_sym {
                                        newcfp.fws.insert(self.the_symbols.get(k).index);
                                    }
                                    broken = true;
                                    break;
                                }
                                NonTerminal {
                                    first_set, lambda, ..
                                } => {
                                    let mut newcfp = self.the_configs.get_mut(newcfp);
                                    newcfp.fws.extend(first_set);
                                    if !lambda {
                                        broken = true;
                                        break;
                                    }
                                }
                            }
                        }
                        if !broken {
                            self.the_configs.get_mut(cfp).fplp.push(newcfp);
                        }
                    }
                }
            }
            i += 1;
        }

        Ok(cur)
    }

    fn add_config(&mut self, cfgs: &mut Vec<ConfigId>, rule: RuleId, dot: usize) -> ConfigId {
        match cfgs.iter().position(|x| {
            config_cmp_key(self, *x, self.the_rules.get(rule).index, dot) == Ordering::Equal
        }) {
            Some(i) => cfgs[i],
            None => {
                let c = Config {
                    rule,
                    dot,
                    fws: RuleSet::new(),
                    fplp: Vec::new(),
                    bplp: Vec::new(),
                    //stp: None,
                    status: CfgStatus::Incomplete,
                };
                let id = self.the_configs.push(c);
                cfgs.push(id);
                id
            }
        }
    }

    fn symbol_new_s(&mut self, name: &str, typ: NewSymbolType) -> SymbolId {
        self.symbol_new(name, typ)
    }
    fn symbol_new_t(&mut self, name: &Ident, typ: NewSymbolType) -> SymbolId {
        self.symbol_new(name.to_string().as_ref(), typ)
    }
    fn symbol_new_t_span(&mut self, name: &Ident, typ: NewSymbolType) -> SymbolSpan {
        let sym = self.symbol_new_t(name, typ);
        SymbolSpan(sym, name.span())
    }
    fn symbol_new(&mut self, name: &str, typ: NewSymbolType) -> SymbolId {
        if !name.is_empty() {
            for s in &self.symbols {
                let mut b = self.the_symbols.get_mut(s);
                if b.name == name {
                    b.use_cnt += 1;
                    //If asked for a MultiTerminal, but it is a Terminal, convert it
                    if let NewSymbolType::MultiTerminal = typ {
                        match b.typ {
                            MultiTerminal { .. } => (),
                            Terminal => {
                                b.typ = MultiTerminal(Vec::new());
                            }
                            _ => unreachable!(),
                        }
                    }
                    return *s;
                }
            }
        }
        let typ = match typ {
            NewSymbolType::Terminal => Terminal,
            NewSymbolType::NonTerminal => NonTerminal {
                rules: Vec::new(),
                first_set: RuleSet::new(),
                lambda: false,
            },
            NewSymbolType::MultiTerminal => MultiTerminal(Vec::new()),
        };
        let symbol = Symbol {
            name: name.to_string(),
            index: 0,
            typ,
            fallback: None,
            precedence: None,
            use_cnt: 1,
            data_type: None,
            dt_num: 0,
            attributes: Vec::new(),
        };

        let id = self.the_symbols.push(symbol);
        self.symbols.push(id);
        id
    }
    fn symbol_find(&self, name: &str) -> Option<SymbolId> {
        for s in &self.symbols {
            let b = self.the_symbols.get(s);
            if b.name == name {
                return Some(*s);
            }
        }
        None
    }

    /*
     ** Compare two states for sorting purposes.  The smaller state is the
     ** one with the most non-terminal actions.  If they have the same number
     ** of non-terminal actions, then the smaller is the one with the most
     ** token actions.
     */
    fn state_resort_cmp(&self, a: StateId, b: StateId) -> Ordering {
        let a = self.the_states.get(a);
        let b = self.the_states.get(b);
        (b.n_nt_act, b.n_tkn_act, b.state_num).cmp(&(a.n_nt_act, a.n_tkn_act, a.state_num))
    }

    fn parse_one_decl(&mut self, pdt: &mut ParserData, decl: Decl) -> syn::Result<()> {
        //println!("PARSE {:?}", decl);
        match decl {
            Decl::Module(id) => {
                self.module = id;
            }
            Decl::Include(code) => {
                self.includes.extend(code);
            }
            Decl::SyntaxError(code) => {
                if self.syntax_error.is_some() {
                    return error_span(code.span(), "Syntax error code already defined");
                }
                self.syntax_error = Some(code);
            }
            Decl::ParseFail(code) => {
                if self.parse_fail.is_some() {
                    return error_span(code.span(), "Parse fail code already defined");
                }
                self.parse_fail = Some(code);
            }
            Decl::StackOverflow(code) => {
                if self.stack_overflow.is_some() {
                    return error_span(code.span(), "Stack overflow code already defined");
                }
                self.stack_overflow = Some(code);
            }
            Decl::Type(attrs, id, ty) => {
                let nst = if is_terminal_ident(&id) {
                    NewSymbolType::Terminal
                } else if is_nonterminal_ident(&id) {
                    if !attrs.is_empty() {
                        return error_span(
                            attrs[0].span(),
                            "Non terminal symbol cannot have attributes",
                        );
                    }
                    NewSymbolType::NonTerminal
                } else {
                    return error_span(
                        id.span(),
                        "Symbol must start with uppercase or lowercase letter",
                    ); //tested
                };
                let sp = self.symbol_new_t(&id, nst);
                let mut sp = self.the_symbols.get_mut(sp);
                if sp.data_type.is_some() {
                    return error_span(id.span(), "Symbol type already defined");
                    //tested
                }
                sp.data_type = ty;
                sp.attributes = attrs;
            }
            Decl::Assoc(a, ids) => {
                pdt.precedence += 1;
                for token in ids {
                    if !is_terminal_ident(&token) {
                        return error_span(
                            token.span(),
                            "Precedence cannot be assigned to a non-terminal",
                        ); //tested
                    }
                    let sp = self.symbol_new_t(&token, NewSymbolType::Terminal);
                    let mut b = self.the_symbols.get_mut(sp);
                    match b.precedence {
                        Some(_) => {
                            return error_span(
                                token.span(),
                                "Symbol has already been given a precedence",
                            )
                        } //tested
                        None => b.precedence = Some(Precedence(pdt.precedence, a)),
                    }
                }
            }
            Decl::DefaultType(ty) => {
                if self.default_type.is_some() {
                    return error_span(ty.span(), "Default type already defined");
                    //tested
                }
                self.default_type = Some(ty);
            }
            Decl::ExtraArgument(ty) => {
                if self.arg.is_some() {
                    return error_span(ty.span(), "Extra argument type already defined");
                    //tested
                }
                self.arg = Some(ty);
            }
            Decl::Error(ty) => {
                if self.err_type.is_some() {
                    return error_span(ty.span(), "Error type already defined"); //tested
                }
                self.err_type = Some(ty);
            }
            Decl::StartSymbol(id) => {
                if self.start.is_some() {
                    return error_span(id.span(), "Start symbol already defined");
                    //tested
                }
                if !is_nonterminal_ident(&id) {
                    return error_span(id.span(), "Start symbol must be a non-terminal");
                    //tested
                }
                self.start = Some(self.symbol_new_t(&id, NewSymbolType::NonTerminal));
            }
            Decl::Fallback(fb, ids) => {
                let mut syms = Vec::with_capacity(ids.len());
                for id in ids {
                    if !is_terminal_ident(&id) {
                        return error_span(id.span(), "Fallback ids must be tokens");
                        //tested
                    }
                    let sp = self.symbol_new_t(&id, NewSymbolType::Terminal);
                    syms.push((id.span(), sp));
                }

                if !is_terminal_ident(&fb) {
                    return error_span(fb.span(), "Fallback must be a token"); //tested
                }

                let fallback = self.symbol_new_t(&fb, NewSymbolType::Terminal);

                // Check that the new fallbacks do not create a fallback-loop.
                // That would cause a stack overflow in runtime.
                {
                    let mut fallback = fallback;
                    loop {
                        let fb_b = self.the_symbols.get(fallback);
                        match fb_b.fallback {
                            None => break,
                            Some(fb_next) => {
                                if syms.iter().any(|(_, s)| *s == fb_next) {
                                    return error_span(
                                        fb.span(),
                                        "Fallback directive creates a loop",
                                    );
                                    //tested
                                }
                                fallback = fb_next;
                            }
                        }
                    }
                }

                let mut has_fallback = self.has_fallback;
                for (span, sp) in syms {
                    let mut b = self.the_symbols.get_mut(sp);
                    if b.fallback.is_some() {
                        return error_span(span, "More than one fallback assigned to token");
                        //tested
                    }
                    b.fallback = Some(fallback);
                    has_fallback = true;
                }
                self.has_fallback = has_fallback;
            }
            Decl::Wildcard(id) => {
                if self.wildcard.is_some() {
                    return error_span(id.span(), "Wildcard already defined"); //tested
                }
                if !is_terminal_ident(&id) {
                    return error_span(id.span(), "Wildcard must be a token"); //tested
                }
                let sp = self.symbol_new_t(&id, NewSymbolType::Terminal);
                self.wildcard = Some(sp);
            }
            Decl::TokenClass(tk, ids) => {
                if !is_terminal_ident(&tk) {
                    return error_span(tk.span(), "token_class must be a token");
                    //tested
                }
                let tk = self.symbol_new_t(&tk, NewSymbolType::MultiTerminal);
                for id in ids {
                    if !is_terminal_ident(&id) {
                        return error_span(id.span(), "token_class ids must be tokens");
                        //tested
                    }
                    let sp = self.symbol_new_t(&id, NewSymbolType::Terminal);
                    if let MultiTerminal(sub_sym) = &mut self.the_symbols.get_mut(tk).typ {
                        sub_sym.push(sp);
                    } else {
                        unreachable!();
                    }
                }
            }
            Decl::Token(e) => {
                if self.token_enum.is_some() {
                    return error_span(e.span(), "token enum already defined"); //tested
                }
                self.token_enum = Some(e);
            }
            Decl::Parser(e) => {
                if self.parser_struct.is_some() {
                    return error_span(e.span(), "parser struct already defined");
                    //tested
                }
                self.parser_struct = Some(e);
            }
            Decl::ExtraToken(ty) => {
                if self.extra_token.is_some() {
                    return error_span(ty.span(), "Extra token type already defined");
                }
                self.extra_token = Some(ty);
            }
            Decl::StackSize(limit, ty) => {
                if self.stack_type.is_some() {
                    return error_span(ty.span(), "Stack size already defined");
                }
                self.stack_limit = limit;
                self.stack_type = ty;
            }
            Decl::Verbose => {
                self.verbose = true;
            }
            Decl::Rule {
                lhs,
                rhs,
                action,
                prec,
            } => {
                let lhs_span = lhs.span();
                if !is_nonterminal_ident(&lhs) {
                    return error_span(lhs_span, "LHS of rule must be non-terminal");
                    //tested
                }
                let lhs = self.symbol_new_t_span(&lhs, NewSymbolType::NonTerminal);
                let rhs = rhs
                    .into_iter()
                    .map(|(toks, optional, alias)| {
                        let SymbolSpan(tok, span) = if toks.len() == 1 {
                            let tok = toks.into_iter().next().unwrap();
                            let nst = if is_terminal_ident(&tok) {
                                NewSymbolType::Terminal
                            } else if is_nonterminal_ident(&tok) {
                                NewSymbolType::NonTerminal
                            } else {
                                return error_span(
                                    tok.span(),
                                    "Symbol must start with uppercase or lowercase letter",
                                ); //tested
                            };
                            if optional {
                                let sym_r = self.symbol_new_t(&tok, nst);
                                if let Some(sym_l) = self.optional_tokens.get(&sym_r) {
                                    sym_l.clone()
                                } else {
                                    let sym_l = self.symbol_new_s(
                                        &format!("_{}", self.optional_tokens.len()),
                                        NewSymbolType::NonTerminal,
                                    );
                                    let sym_l = SymbolSpan(sym_l, tok.span());
                                    self.optional_tokens.insert(sym_r, sym_l.clone());
                                    sym_l
                                }
                            } else {
                                self.symbol_new_t_span(&tok, nst)
                            }
                        } else {
                            let mt = self.symbol_new_s("", NewSymbolType::MultiTerminal);
                            let mut ss = Vec::new();
                            let span = toks[0].span(); //TODO: extend span
                            for tok in toks {
                                if !is_terminal_ident(&tok) {
                                    return error_span(
                                        tok.span(),
                                        "Cannot form a compound containing a non-terminal",
                                    ); //tested
                                }
                                ss.push(self.symbol_new_t(&tok, NewSymbolType::Terminal));
                            }
                            if let MultiTerminal(sub_sym) = &mut self.the_symbols.get_mut(mt).typ {
                                sub_sym.extend(ss);
                            } else {
                                unreachable!();
                            }
                            SymbolSpan(mt, span)
                        };
                        Ok(SymbolAlias(tok, span, alias))
                    })
                    .collect::<syn::Result<Vec<_>>>()?;

                let prec_sym = match &prec {
                    Some(id) => {
                        if !is_terminal_ident(id) {
                            return error_span(id.span(), "The precedence symbol must be a token");
                            //tested
                        }
                        Some(self.symbol_new_t(id, NewSymbolType::Terminal))
                    }
                    None => None,
                };

                self.create_rule(lhs_span, lhs, rhs, action, prec_sym);
            }
        }
        Ok(())
    }

    fn create_rule(
        &mut self,
        span: Span,
        lhs: SymbolSpan,
        rhs: Vec<SymbolAlias>,
        code: Option<Block>,
        prec_sym: Option<SymbolId>,
    ) {
        let index = self.rules.len();
        let rule = Rule {
            span,
            lhs,
            lhs_start: false,
            rhs,
            code,
            prec_sym,
            precedence: None,
            index,
            can_reduce: false,
        };
        let id = self.the_rules.push(rule);
        let rule = self.the_rules.get_mut(id);

        if let NonTerminal { rules, .. } = &mut self.the_symbols.get_mut(rule.lhs.0).typ {
            rules.push(id);
        } else {
            unreachable!("lhs is not a non-terminal");
        }
        self.rules.push(id);
    }

    fn generate_source(&mut self) -> syn::Result<TokenStream> {
        let mut src = TokenStream::new();
        src.extend(quote! {
            #![allow(dead_code)]
            #![allow(unreachable_code)]
            #![allow(unused_variables)]
            #![allow(non_snake_case)]
            #![allow(unused_braces)]
            #![allow(unused_mut)]
            #![allow(clippy::let_unit_value)]
        });

        for code in &self.includes {
            code.to_tokens(&mut src);
        }

        /* Generate the defines */
        let yycodetype = minimum_signed_type(self.symbols.len());
        let yyactiontype = minimum_unsigned_type(self.states.len() + self.rules.len() + 5);
        let yynocode = (self.symbols.len()) as i32;
        let yywildcard = if let Some(wildcard) = self.wildcard {
            let wildcard = self.the_symbols.get(wildcard);
            if let Some(dt) = &wildcard.data_type {
                return error_span(dt.span(), "Wildcard token must not have a type");
                //tested
            }
            wildcard.index
        } else {
            0
        };
        let yywildcard = Literal::usize_unsuffixed(yywildcard);

        let yystacktype = match self.stack_type {
            Some(ref ty) => Cow::Borrowed(ty),
            None => Cow::Owned(parse_quote!(std::vec::Vec)),
        };
        let yystacklimit = self.stack_limit;

        src.extend(quote! {
            const YYNOCODE: i32 = #yynocode;
            const YYWILDCARD: #yycodetype = #yywildcard;
            type YYStack<T> = #yystacktype<T>;
            const YYSTACKLIMIT: usize = #yystacklimit;
        });

        /*
         ** Print the definition of the union used for the parser's data stack.
         ** This union contains fields for every possible data type for tokens
         ** and nonterminals.  In the process of computing and printing this
         ** union, also set the ".dt_num" field of every terminal and nonterminal
         ** symbol.
         */
        //Maps the Type to the equivalent dt_num
        let mut types = HashMap::<Type, usize>::new();

        for sp in &self.symbols {
            if let Some(wildcard) = &self.wildcard {
                if sp == wildcard {
                    continue;
                }
            }

            let mut sp = self.the_symbols.get_mut(sp);

            /* Determine the data_type of each symbol and fill its dt_num */
            let data_type = match &sp.typ {
                SymbolType::MultiTerminal(ss) => {
                    //MultiTerminals have the type of the first child.
                    //The type of the children need be the same only if an alias is used, so we
                    //cannot check it here
                    let first = self.the_symbols.get(ss.first().unwrap());
                    first.data_type.clone()
                }
                SymbolType::Terminal => sp.data_type.clone(),
                SymbolType::NonTerminal { .. } => sp.data_type.clone(),
            };

            sp.data_type = data_type.or_else(|| self.default_type.clone());
            sp.dt_num = match &sp.data_type {
                None => 0,
                Some(cp) => {
                    let next = types.len() + 1;
                    *types.entry(cp.clone()).or_insert(next)
                }
            };
        }

        let mut yytoken = self
            .token_enum
            .clone()
            .unwrap_or_else(|| parse_quote! { pub enum Token{} });

        if !yytoken.variants.is_empty() {
            return error_span(
                yytoken.variants.span(),
                "Token enum declaration must be empty",
            ); //tested
        }
        let (yy_generics_impl_token, yy_generics_token, yy_generics_where_token) =
            yytoken.generics.split_for_impl();

        //If %parser is not used, then use a default Parser with the same generics as the Token
        let mut yyparser = self.parser_struct.
            clone().
            unwrap_or_else(|| parse_quote!{ pub struct Parser #yy_generics_impl_token #yy_generics_where_token { } });

        if let Some(f) = yyparser.fields.iter().next() {
            return error_span(f.span(), "Parser struct declaration must be empty");
            //tested
        }

        for g in yytoken.generics.params.iter() {
            if !yyparser.generics.params.iter().any(|p| p == g) {
                return error_span(g.span(), "Generic parameter in Token is not in Parser");
                //tested
            }
        }
        let (yy_generics_impl, yy_generics, yy_generics_where) = yyparser.generics.split_for_impl();

        let yysyntaxerror = match self.syntax_error {
            Some(ref c) => Cow::Borrowed(c),
            None => Cow::Owned(parse_quote!({ Err(Default::default()) })),
        };
        let yyparsefail = match self.parse_fail {
            Some(ref c) => Cow::Borrowed(c),
            None => Cow::Owned(parse_quote!({ Default::default() })),
        };
        let yystackoverflow = match self.stack_overflow {
            Some(ref c) => Cow::Borrowed(c),
            None => {
                //stack_limit == 0, means unlimited, so the code will never be called
                let c = if self.stack_limit == 0 {
                    parse_quote!({ unreachable!() })
                } else {
                    parse_quote!({ Default::default() })
                };
                Cow::Owned(c)
            }
        };

        let minor_types = types.iter().map(|(k, v)| {
            let ident = Ident::new(&format!("YY{}", v), Span::call_site());
            quote!(#ident(#k))
        });
        src.extend(quote!(
            enum YYMinorType #yy_generics_impl
                #yy_generics_where
            {
                YY_(::core::marker::PhantomData<Parser #yy_generics>),
                YY0(()),
                #(#minor_types),*
            }
        ));

        let error_symbol = self.the_symbols.get(self.error_symbol);
        let yynstate = Literal::usize_unsuffixed(self.states.len());
        let yynrule = Literal::usize_unsuffixed(self.rules.len());
        let yyerrorsymbol = if error_symbol.use_cnt > 1 {
            error_symbol.index
        } else {
            0
        };
        let yyerrorsymbol = Literal::usize_unsuffixed(yyerrorsymbol);

        src.extend(quote!(
            const YYNSTATE: i32 = #yynstate;
            const YYNRULE: i32 = #yynrule;
            const YYERRORSYMBOL: i32 = #yyerrorsymbol;
        ));

        /* Generate the action table and its associates:
         **
         **  yy_action[]        A single table containing all actions.
         **  yy_lookahead[]     A table containing the lookahead for each entry in
         **                     yy_action.  Used to detect hash collisions.
         **  yy_shift_ofst[]    For each state, the offset into yy_action for
         **                     shifting terminals.
         **  yy_reduce_ofst[]   For each state, the offset into yy_action for
         **                     shifting non-terminals after a reduce.
         **  yy_default[]       Default action for each state.
         */

        let mut ax = Vec::with_capacity(2 * self.states.len());
        /* Compute the actions on all states and count them up */
        for stp in &self.states {
            ax.push(AxSet {
                stp: *stp,
                is_tkn: true,
                n_action: self.the_states.get(stp).n_tkn_act,
            });
            ax.push(AxSet {
                stp: *stp,
                is_tkn: false,
                n_action: self.the_states.get(stp).n_nt_act,
            });
        }

        ax.sort_by_key(|a| a.n_action);
        ax.reverse();

        let mut max_tkn_ofst = 0;
        let mut min_tkn_ofst = 0;
        let mut max_nt_ofst = 0;
        let mut min_nt_ofst = 0;

        /* Compute the action table.  In order to try to keep the size of the
         ** action table to a minimum, the heuristic of placing the largest action
         ** sets first is used.
         */
        let mut acttab = ActTab::new();

        for a in &ax {
            let mut actset = ActionSet::new();

            if a.n_action == 0 {
                continue;
            }
            if a.is_tkn {
                for ap in &self.the_states.get(a.stp).actions {
                    let ap = ap.borrow();
                    let sp = self.the_symbols.get(ap.look_ahead);
                    if sp.index >= self.num_terminals {
                        continue;
                    }
                    match self.compute_action(&ap) {
                        None => continue,
                        Some(action) => actset.add_action(sp.index, action),
                    }
                }
                let ofs = acttab.insert_action_set(&actset);
                let mut stp = self.the_states.get_mut(a.stp);
                stp.i_tkn_ofst = Some(ofs);
                min_tkn_ofst = cmp::min(ofs, min_tkn_ofst);
                max_tkn_ofst = cmp::max(ofs, max_tkn_ofst);
            } else {
                for ap in &self.the_states.get(a.stp).actions {
                    let ap = ap.borrow();
                    let sp = self.the_symbols.get(ap.look_ahead);
                    if sp.index < self.num_terminals {
                        continue;
                    }
                    if sp.index == self.default_index {
                        continue;
                    }
                    //sp is a non-default NonTerminal
                    match self.compute_action(&ap) {
                        None => continue,
                        Some(action) => actset.add_action(sp.index, action),
                    }
                }
                let ofs = acttab.insert_action_set(&actset);
                let mut stp = self.the_states.get_mut(a.stp);
                stp.i_nt_ofst = Some(ofs);
                min_nt_ofst = cmp::min(ofs, min_nt_ofst);
                max_nt_ofst = cmp::max(ofs, max_nt_ofst);
            }
        }
        /* Output the yy_action table */
        let yytoken_span = yytoken.brace_token.span;

        let mut token_matches = Vec::new();
        let mut token_builds = Vec::new();
        let mut token_extra = Vec::new();
        let mut token_names = vec!["(eoi)".to_string()];
        for i in 1..self.num_terminals {
            let s = self.the_symbols.get(self.symbols[i]);
            let i = i as i32;
            let name = Ident::new(&s.name, Span::call_site());
            token_names.push(s.name.clone());
            let yydt = Ident::new(&format!("YY{}", s.dt_num), Span::call_site());
            let dt = match &s.data_type {
                Some(dt) => {
                    token_matches.push(quote!(Token::#name(x) => (#i, YYMinorType::#yydt(x))));
                    token_builds.push(quote!((#i, YYMinorType::#yydt(x)) => Some(Token::#name(x))));

                    if let Some(extra_token) = &self.extra_token {
                        if dt == extra_token {
                            token_extra.push(quote!(Token::#name(e) => e));
                        } else {
                            token_extra.push(quote!(Token::#name((e, _)) => e));
                        }
                    }
                    Fields::Unnamed(parse_quote! { (#dt) })
                }
                None => {
                    token_matches.push(quote!(Token::#name => (#i, YYMinorType::#yydt(()))));
                    token_builds.push(quote!((#i, _) => Some(Token::#name)));
                    Fields::Unit
                }
            };
            yytoken.variants.push(Variant {
                attrs: s.attributes.clone(),
                ident: Ident::new(&s.name, yytoken_span.open()),
                fields: dt,
                discriminant: None,
            });
        }
        token_builds.push(quote!(_ => None));

        src.extend(quote!(
            #yytoken

            #[inline]
            fn token_value #yy_generics_impl(t: Token #yy_generics_token) -> (i32, YYMinorType #yy_generics)
                #yy_generics_where
            {
                match t {
                    #(#token_matches),*
                }
            }
            fn token_build #yy_generics_impl(i: i32, yy: YYMinorType #yy_generics) -> Option<Token #yy_generics_token>
                #yy_generics_where
            {
                match (i, yy) {
                    #(#token_builds),*
                }
            }
        ));

        if let Some(extra_token) = &self.extra_token {
            let token_extra = &token_extra; //so that we can use the same array several times
            src.extend(quote!(
                impl #yy_generics_impl_token Token #yy_generics_token #yy_generics_where_token
                {
                    pub fn into_extra(self) -> #extra_token {
                        match (self) {
                            #(#token_extra),*
                        }
                    }
                    pub fn extra(&self) -> &#extra_token {
                        match (self) {
                            #(#token_extra),*
                        }
                    }
                    pub fn extra_mut(&mut self) -> &mut #extra_token {
                        match (self) {
                            #(#token_extra),*
                        }
                    }
                }
            ));
        }

        let token_names_len = token_names.len();
        src.extend(
            quote!(static YY_TOKEN_NAMES: [&str; #token_names_len] = [ #(#token_names),* ];),
        );

        let yy_action = acttab
            .a_action
            .iter()
            .map(|ac| match ac {
                None => (self.states.len() + self.rules.len() + 2) as i32,
                Some(a) => a.action as i32,
            })
            .map(Literal::i32_unsuffixed);
        let yy_action_len = yy_action.len();
        src.extend(quote!(static YY_ACTION: [i32; #yy_action_len] = [ #(#yy_action),* ];));

        /* Output the yy_lookahead table */
        let yy_lookahead = acttab
            .a_action
            .iter()
            .map(|ac| match ac {
                None => self.default_index,
                Some(a) => a.lookahead,
            })
            .map(Literal::usize_unsuffixed);
        let yy_lookahead_len = yy_lookahead.len();
        src.extend(
            quote!(static YY_LOOKAHEAD: [#yycodetype; #yy_lookahead_len] = [ #(#yy_lookahead),* ];),
        );

        /* Output the yy_shift_ofst[] table */
        let n = self
            .states
            .iter()
            .rposition(|st| self.the_states.get(st).i_tkn_ofst.is_some())
            .unwrap();
        let yy_shift_use_dflt = min_tkn_ofst - 1;
        src.extend(quote!(const YY_SHIFT_USE_DFLT: i32 = #yy_shift_use_dflt;));
        src.extend(quote!(const YY_SHIFT_COUNT: i32 = #n as i32;));
        src.extend(quote!(const YY_SHIFT_MIN: i32 = #min_tkn_ofst;));
        src.extend(quote!(const YY_SHIFT_MAX: i32 = #max_tkn_ofst;));
        let yy_shift_ofst_type = minimum_signed_type(max_tkn_ofst as usize);
        let yy_shift_ofst = self.states[0..=n]
            .iter()
            .map(|stp| {
                let stp = self.the_states.get(stp);
                stp.i_tkn_ofst.unwrap_or(min_tkn_ofst - 1)
            })
            .map(Literal::i32_unsuffixed);
        let yy_shift_ofst_len = yy_shift_ofst.len();
        src.extend(quote!(static YY_SHIFT_OFST: [#yy_shift_ofst_type; #yy_shift_ofst_len] = [ #(#yy_shift_ofst),* ];));

        /* Output the yy_reduce_ofst[] table */
        let n = self
            .states
            .iter()
            .rposition(|st| self.the_states.get(st).i_nt_ofst.is_some())
            .unwrap();
        let yy_reduce_use_dflt = min_nt_ofst - 1;
        src.extend(quote!(const YY_REDUCE_USE_DFLT: i32 = #yy_reduce_use_dflt;));
        src.extend(quote!(const YY_REDUCE_COUNT: i32 = #n as i32;));
        src.extend(quote!(const YY_REDUCE_MIN: i32 = #min_nt_ofst;));
        src.extend(quote!(const YY_REDUCE_MAX: i32 = #max_nt_ofst;));
        let yy_reduce_ofst_type = minimum_signed_type(max_nt_ofst as usize);
        let yy_reduce_ofst = self.states[0..=n]
            .iter()
            .map(|stp| {
                let stp = self.the_states.get(stp);
                stp.i_nt_ofst.unwrap_or(min_nt_ofst - 1)
            })
            .map(Literal::i32_unsuffixed);
        let yy_reduce_ofst_len = yy_reduce_ofst.len();
        src.extend(quote!(static YY_REDUCE_OFST: [#yy_reduce_ofst_type; #yy_reduce_ofst_len] = [ #(#yy_reduce_ofst),* ];));

        let yy_default = self
            .states
            .iter()
            .map(|stp| self.the_states.get(stp).i_dflt)
            .map(Literal::usize_unsuffixed);
        let yy_default_len = yy_default.len();
        src.extend(
            quote!(static YY_DEFAULT: [#yyactiontype; #yy_default_len] = [ #(#yy_default),* ];),
        );

        /* Generate the table of fallback tokens. */
        let mx = self
            .symbols
            .iter()
            .rposition(|sy| self.the_symbols.get(sy).fallback.is_some())
            .map_or(0, |x| x + 1);
        let yy_fallback = self.symbols[0..mx]
            .iter()
            .map(|p| {
                let p = self.the_symbols.get(p);
                match &p.fallback {
                    None => Ok(0),
                    Some(fb) => {
                        let fb = self.the_symbols.get(fb);
                        match (fb.dt_num, p.dt_num) {
                            (0, _) => {}
                            (fdt, pdt) if fdt == pdt => {}
                            _ => {
                                return error_span(
                                    fb.data_type.span(),
                                    "Fallback token must have the same type or no type at all",
                                ); //tested
                            }
                        }
                        Ok(fb.index as i32)
                    }
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
        let yy_fallback_len = yy_fallback.len();
        src.extend(quote!(static YY_FALLBACK: [i32; #yy_fallback_len] = [ #(#yy_fallback),* ];));

        /* Generate the table of rule information
         **
         ** Note: This code depends on the fact that rules are number
         ** sequentually beginning with 0.
         */
        let yy_rule_info = self
            .rules
            .iter()
            .map(|rp| self.the_symbols.get(self.the_rules.get(rp).lhs.0).index)
            .map(Literal::usize_unsuffixed);
        let yy_rule_info_len = yy_rule_info.len();
        src.extend(
            quote!(static YY_RULE_INFO: [#yycodetype; #yy_rule_info_len] = [ #(#yy_rule_info),* ];),
        );

        let unit_type: Type = parse_quote!(());
        let yyextratype = self.arg.as_ref().unwrap_or(&unit_type);
        let start = self.the_symbols.get(self.start.unwrap());
        let yyroottype = start.data_type.as_ref().unwrap_or(&unit_type);
        let yyerrtype = self.err_type.as_ref().unwrap_or(&unit_type);

        let parser_fields = parse_quote!({
            error_count: u8, /* Shift since last error */
            yystack: YYStack<YYStackEntry #yy_generics>,
            extra: #yyextratype,
            yystatus: YYStatus<#yyroottype>,
        });
        yyparser.fields = syn::Fields::Named(parser_fields);

        src.extend(quote! {
            struct YYStackEntry #yy_generics_impl #yy_generics_where
            {
                stateno: i32,   /* The state-number */
                major: i32,     /* The major token value.  This is the code
                                 ** number for the token at this stack level */
                minor: YYMinorType #yy_generics,    /* The user-supplied minor token value.  This
                                                     ** is the value of the token  */
            }

            enum YYStatus<T> {
                Normal,
                Failed,
                Accepted(T),
            }
            impl<T> YYStatus<T> {
                fn unwrap(self) -> T {
                    match self {
                        YYStatus::Accepted(t) => t,
                        _ => unreachable!("accepted without data"),
                    }
                }
                fn is_normal(&self) -> bool {
                    match self {
                        YYStatus::Normal => true,
                        _ => false,
                    }
                }
            }

            #yyparser
        });

        let impl_parser = if *yyextratype == unit_type {
            quote! {
                pub fn new() -> Self {
                    Self::new_priv(())
                }
                pub fn end_of_input(mut self) -> ::core::result::Result<#yyroottype, #yyerrtype> {
                    self.end_of_input_priv().map(|r| r.0)
                }
            }
        } else {
            quote! {
                pub fn new(extra: #yyextratype) -> Self {
                    Self::new_priv(extra)
                }
                pub fn end_of_input(mut self) -> ::core::result::Result<(#yyroottype, #yyextratype), #yyerrtype> {
                    self.end_of_input_priv()
                }
                pub fn into_extra(self) -> #yyextratype {
                    self.extra
                }
                pub fn extra(&self) -> &#yyextratype {
                    &self.extra
                }
                pub fn extra_mut(&mut self) -> &mut #yyextratype {
                    &mut self.extra
                }
            }
        };
        src.extend(quote!{
            impl #yy_generics_impl Parser #yy_generics #yy_generics_where
            {
                #impl_parser
                pub fn parse(&mut self, token: Token #yy_generics_token) -> ::core::result::Result<(), #yyerrtype> {
                    let (a, b) = token_value(token);
                    yy_parse_token(self, a, b)
                }
                fn new_priv(extra: #yyextratype) -> Self {
                    let mut yystack = YYStack::new();
                    yystack.push(YYStackEntry {
                            stateno: 0,
                            major: 0,
                            minor: YYMinorType::YY0(())
                    });
                    Parser {
                        error_count: 0,
                        yystack,
                        extra,
                        yystatus: YYStatus::Normal,
                    }
                }
                fn end_of_input_priv(mut self) -> ::core::result::Result<(#yyroottype, #yyextratype), #yyerrtype> {
                    yy_parse_token(&mut self, 0, YYMinorType::YY0(()))?;
                    Ok((self.yystatus.unwrap(), self.extra))
                }
            }
        });

        src.extend(quote! {
            #[derive(Clone)]
            struct ExpectedTokens #yy_generics_impl #yy_generics_where {
                stateno: i32,
                yy_major: i32,
                _phantom: ::std::marker::PhantomData<Parser #yy_generics>,
            }

            struct ExpectedToken #yy_generics_impl_token #yy_generics_where_token {
                name: &'static str,
                yy_major: i32,
                token: Option<Token #yy_generics_token>,
            }

            impl #yy_generics_impl Iterator for ExpectedTokens #yy_generics #yy_generics_where {
                type Item = ExpectedToken #yy_generics_token;

                fn next(&mut self) -> Option<Self::Item> {
                    use std::convert::TryFrom;
                    loop {
                        let yy_major = self.yy_major;
                        let name = *YY_TOKEN_NAMES.get(usize::try_from(yy_major).unwrap())?;
                        self.yy_major += 1;
                        if yy_find_shift_action_2(self.stateno, yy_major) < YYNSTATE + YYNRULE {
                            let yy0: YYMinorType #yy_generics = YYMinorType::YY0(());
                            let token = token_build(yy_major, yy0);
                            return Some(ExpectedToken { name, yy_major, token })
                        }
                    }
                }
            }
        });

        src.extend(quote!{
            fn yy_parse_token #yy_generics_impl(yy: &mut Parser #yy_generics,
                                                        yymajor: i32, yyminor: YYMinorType #yy_generics) -> ::core::result::Result<(), #yyerrtype>
                #yy_generics_where
            {
                if !yy.yystatus.is_normal() {
                    panic!("Cannot call parse after failure");
                }
                let res = yy_parse_token_2(yy, yymajor, yyminor);
                if res.is_err() {
                    yy.yystatus = YYStatus::Failed;
                }
                res
            }
            fn yy_parse_token_2 #yy_generics_impl(yy: &mut Parser #yy_generics,
                                                        yymajor: i32, yyminor: YYMinorType #yy_generics) -> ::core::result::Result<(), #yyerrtype>
                #yy_generics_where
            {

                while yy.yystatus.is_normal() {
                    let yyact = yy_find_shift_action(yy, yymajor);
                    if yyact < YYNSTATE {
                        assert!(yymajor != 0);  /* Impossible to shift the $ token */
                        yy_shift(yy, yyact, yymajor, yyminor)?;
                        yy.error_count = yy.error_count.saturating_sub(1);
                        break;
                    } else if yyact < YYNSTATE + YYNRULE {
                        yy_reduce(yy, yyact - YYNSTATE)?;
                    } else {
                        /* A syntax error has occurred.
                         ** The response to an error depends upon whether or not the
                         ** grammar defines an error token "ERROR".
                         */
                        assert!(yyact == YYNSTATE+YYNRULE);

                        /* Generate a list of tokens that would have been acceptable at this point.
                         ** This will be fed to %syntax_error to allow producing more human-readable
                         ** errors.
                         */
                        let expected = ExpectedTokens {
                            stateno: yy.yystack.last().unwrap().stateno,
                            yy_major: 1,
                            _phantom: ::std::marker::PhantomData,
                        };

                        if YYERRORSYMBOL != 0 {
                            /* This is what we do if the grammar does define ERROR:
                             **
                             **  * Begin popping the stack until we enter either:
                             **     - we find the error symbol: discard the input token.
                             **     - we get into a state where it is legal to shift the
                             **       error symbol: we call %syntax_error and use the result
                             **       to create an shift the error symbol.
                             **     - we empty the stack: we fail the parse.
                             **
                             **  * Begin accepting and shifting new tokens.
                             */
                            if yymajor == 0 { //EOI
                                return Err(yy_parse_failed(yy));
                            }
                            while let Some(top) = yy.yystack.last() {
                                if top.major == YYERRORSYMBOL { break; }

                                let yyact = yy_find_reduce_action(yy, YYERRORSYMBOL);
                                if yyact < YYNSTATE {
                                    let e = yy_syntax_error(yy, yymajor, yyminor, expected)?;
                                    yy_shift(yy, yyact, YYERRORSYMBOL, e)?;
                                    break;
                                }
                                yy.yystack.pop().unwrap();
                            }
                            if yy.yystack.is_empty() {
                                return Err(yy_parse_failed(yy));
                            }
                            yy.error_count = 3;
                            break;
                        } else {
                            /* This is what we do if the grammar does not define ERROR:
                             **
                             **  * Report an error message, and throw away the input token.
                             **
                             **  * If the input token is $, then fail the parse.
                             **
                             ** As before, subsequent error messages are suppressed until
                             ** three input tokens have been successfully shifted.
                             */
                            if yymajor == 0 { //EOI
                                return Err(yy_parse_failed(yy));
                            }
                            if yy.error_count == 0 {
                                yy_syntax_error(yy, yymajor, yyminor, expected)?;
                            }
                            yy.error_count = 3;
                            break;
                        }
                    }
                }
                Ok(())
            }

            /*
             ** Find the appropriate action for a parser given the terminal
             ** look-ahead token look_ahead.
             */
            fn yy_find_shift_action #yy_generics_impl(yy: &mut Parser #yy_generics, look_ahead: i32) -> i32 #yy_generics_where
            {
                yy_find_shift_action_2(yy.yystack.last().unwrap().stateno, look_ahead)
            }

            fn yy_find_shift_action_2(stateno: i32, look_ahead: i32) -> i32
            {
                if stateno > YY_SHIFT_COUNT {
                    return YY_DEFAULT[stateno as usize] as i32;
                }
                let i = YY_SHIFT_OFST[stateno as usize] as i32;
                if i == YY_SHIFT_USE_DFLT {
                    return YY_DEFAULT[stateno as usize] as i32;
                }
                assert!(look_ahead != YYNOCODE);
                let i = i + look_ahead;

                if i < 0 || i >= YY_ACTION.len() as i32 || YY_LOOKAHEAD[i as usize] as i32 != look_ahead {
                    if look_ahead > 0 {
                        if (look_ahead as usize) < YY_FALLBACK.len() {
                            let fallback = YY_FALLBACK[look_ahead as usize];
                            if fallback != 0 {
                                return yy_find_shift_action_2(stateno, fallback);
                            }
                        }
                        if YYWILDCARD > 0 {
                            let j = i - look_ahead + (YYWILDCARD as i32);
                            if j >= 0 && j < YY_ACTION.len() as i32 && YY_LOOKAHEAD[j as usize]==YYWILDCARD {
                                return YY_ACTION[j as usize] as i32;
                            }
                        }
                    }
                    return YY_DEFAULT[stateno as usize] as i32;
                } else {
                    return YY_ACTION[i as usize] as i32;
                }
            }

            /*
             ** Find the appropriate action for a parser given the non-terminal
             ** look-ahead token iLookAhead.
             */
            fn yy_find_reduce_action #yy_generics_impl(yy: &mut Parser #yy_generics, look_ahead: i32) -> i32 #yy_generics_where
            {
                let stateno = yy.yystack.last().unwrap().stateno;
                if YYERRORSYMBOL != 0 && stateno > YY_REDUCE_COUNT {
                    return YY_DEFAULT[stateno as usize] as i32;
                }
                assert!(stateno <= YY_REDUCE_COUNT);
                let i = YY_REDUCE_OFST[stateno as usize] as i32;
                assert!(i != YY_REDUCE_USE_DFLT);
                assert!(look_ahead != YYNOCODE );
                let i = i + look_ahead;
                if YYERRORSYMBOL != 0 && (i < 0 || i >= YY_ACTION.len() as i32 || YY_LOOKAHEAD[i as usize] as i32 != look_ahead) {
                    return YY_DEFAULT[stateno as usize] as i32;
                }
                assert!(i >= 0 && i < YY_ACTION.len() as i32);
                assert!(YY_LOOKAHEAD[i as usize] as i32 == look_ahead);
                return YY_ACTION[i as usize] as i32;
            }
        });
        let ty_span = yystackoverflow.span();
        src.extend(quote_spanned!{ty_span=>
            fn yy_shift #yy_generics_impl(yy: &mut Parser #yy_generics, new_state: i32, yymajor: i32, yyminor: YYMinorType #yy_generics) -> ::core::result::Result<(), #yyerrtype>
                #yy_generics_where
            {
                if YYSTACKLIMIT != 0 && yy.yystack.len() >= YYSTACKLIMIT {
                    let token = token_build(yymajor, yyminor);
                    let extra = &mut yy.extra;
                    return Err(#yystackoverflow);
                }
                yy.yystack.push(YYStackEntry {
                    stateno: new_state,
                    major: yymajor,
                    minor: yyminor});
                Ok(())
            }
        });
        let ty_span = yyparsefail.span();
        src.extend(quote_spanned! {ty_span=>
            fn yy_parse_failed #yy_generics_impl(yy: &mut Parser #yy_generics) -> #yyerrtype
                #yy_generics_where
            {
                yy.yystack.clear();
                let extra = &mut yy.extra;
                #yyparsefail
            }
        });

        let error_ty = error_symbol.data_type.as_ref().unwrap_or(&unit_type);
        let error_yydt = Ident::new(&format!("YY{}", error_symbol.dt_num), Span::call_site());
        let ty_span = yysyntaxerror.span();
        src.extend(quote_spanned!{ty_span=>
            fn yy_syntax_error_2 #yy_generics_impl(yy: &mut Parser #yy_generics, yymajor: i32, yyminor: YYMinorType #yy_generics, expected: ExpectedTokens #yy_generics) -> ::core::result::Result<#error_ty, #yyerrtype>
                #yy_generics_where
            {
                let token = token_build(yymajor, yyminor);
                let extra = &mut yy.extra;
                let mut expected = expected;
                #yysyntaxerror
            }
            fn yy_syntax_error #yy_generics_impl(yy: &mut Parser #yy_generics, yymajor: i32, yyminor: YYMinorType #yy_generics, expected: ExpectedTokens #yy_generics) -> ::core::result::Result<YYMinorType #yy_generics, #yyerrtype>
                #yy_generics_where
            {
                let e = yy_syntax_error_2(yy, yymajor, yyminor, expected)?;
                Ok(YYMinorType::#error_yydt(e))
            }
        });

        /* Generate code which execution during each REDUCE action */
        /* First output rules other than the default: rule */
        //TODO avoid dumping the same code twice
        let mut yyrules = Vec::new();
        for rp in &self.rules {
            let rp = self.the_rules.get(rp);
            let code = self.translate_code(&rp)?;
            let index = rp.index as i32;

            //Use quote_spanned! to inject `extra` into the `code` rule
            let ty_span = rp.code.span();
            yyrules.push(quote_spanned!(ty_span=> (#index, extra) => { #code }));
        }
        yyrules.push(quote!(_ => unreachable!("no rule to apply")));

        let accept_code = match types.get(yyroottype) {
            Some(n) => {
                let yyroot = Ident::new(&format!("YY{}", n), Span::call_site());
                quote!(
                    if let YYMinorType::#yyroot(root) = yygotominor {
                        yy.yystatus = YYStatus::Accepted(root);
                        yy.yystack.clear();
                    } else {
                        unreachable!("unexpected root type");
                    }
                )
            }
            None => quote!(
                yy.yystatus = YYStatus::Accepted(());
                yy.yystack.clear();
            ),
        };

        let yyreduce_fn = quote!(
            fn yy_reduce #yy_generics_impl(yy: &mut Parser #yy_generics, yyruleno: i32) -> ::core::result::Result<(), #yyerrtype>
                #yy_generics_where
            {
                let yygotominor: YYMinorType #yy_generics = match (yyruleno, &mut yy.extra) {
                    #(#yyrules)*
                };
                let yygoto = YY_RULE_INFO[yyruleno as usize] as i32;
                let yyact = yy_find_reduce_action(yy, yygoto);
                if yyact < YYNSTATE {
                    yy_shift(yy, yyact, yygoto, yygotominor)?;
                    Ok(())
                } else {
                    assert!(yyact == YYNSTATE + YYNRULE + 1);
                    #accept_code
                    Ok(())
                }
            }
        );
        yyreduce_fn.to_tokens(&mut src);

        Ok(src)
    }

    fn translate_code(&self, rp: &Rule) -> syn::Result<TokenStream> {
        let lhs = self.the_symbols.get(rp.lhs.0);
        let mut code = TokenStream::new();

        for i in (0..rp.rhs.len()).rev() {
            let yypi = Ident::new(&format!("yyp{}", i), Span::call_site());
            code.extend(quote!(let #yypi = yy.yystack.pop().unwrap();));
        }

        let unit_type = parse_quote!(());
        let yyrestype = lhs.data_type.as_ref().unwrap_or(&unit_type);

        let mut yymatch = Vec::new();
        for (i, SymbolAlias(r, _, alias)) in rp.rhs.iter().enumerate() {
            let r = self.the_symbols.get(r);
            let yypi = Ident::new(&format!("yyp{}", i), Span::call_site());
            yymatch.push(quote!(#yypi.minor));
            if let (Some(alias), MultiTerminal(ss)) = (alias, &r.typ) {
                for or in &ss[1..] {
                    if r.dt_num != self.the_symbols.get(or).dt_num {
                        return error_span(
                            alias.span(),
                            "Compound tokens with an alias must all have the same type",
                        ); //tested
                    }
                }
            }
        }

        let mut yypattern = Vec::new();
        for SymbolAlias(r, _, alias) in &rp.rhs {
            let yydt = Ident::new(
                &format!("YY{}", self.the_symbols.get(r).dt_num),
                Span::call_site(),
            );
            match alias {
                Some(alias) => {
                    if Some(r) == self.wildcard.as_ref() {
                        return error_span(alias.span(), "Wildcard token must not have an alias");
                        //tested
                    }
                    yypattern.push(quote!(YYMinorType::#yydt(#alias)))
                }
                None => yypattern.push(quote!(_)),
            }
        }

        let rule_code = rp.code.as_ref();
        code.extend(quote!(
            let yyres : #yyrestype = match (#(#yymatch),*) {
                (#(#yypattern),*) => { #rule_code }
                _ => unreachable!("impossible pattern")
            };
        ));

        let yydt = Ident::new(&format!("YY{}", lhs.dt_num), Span::call_site());
        code.extend(quote!(YYMinorType::#yydt(yyres)));
        Ok(code)
    }
}
