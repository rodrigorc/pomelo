use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;
use std::cell::RefCell;
use std::io;
use std::cmp::{self, Ordering};
use std::fmt;

use syn;
use quote::ToTokens;
use decl::*;

mod wrc;
use self::wrc::WRc;

type RuleSet = BTreeSet<usize>;

enum NewSymbolType {
    Terminal,
    NonTerminal,
    MultiTerminal,
}

#[derive(Debug, Copy, Clone)]
struct Precedence(i32, Associativity);

fn precedence_cmp(a: &Precedence, b: &Precedence) -> Ordering {
	match a.0.cmp(&b.0) {
        Ordering::Equal => {
            match a.1 {
                Associativity::Left => Ordering::Less,
                Associativity::Right => Ordering::Greater,
                Associativity::None => Ordering::Equal,
            }
        }
        o => o
	}
}

#[derive(Debug)]
struct Rule {
    lhs: WRc<RefCell<Symbol>>,  //Left-hand side of the rule
    lhs_start: bool,    //True if LHS is the start symbol
    rhs: Vec<(WRc<RefCell<Symbol>>, Option<String>)>,   //RHS symbols and aliases
    code: Option<Group>,//The code executed when this rule is reduced
    prec_sym: Option<WRc<RefCell<Symbol>>>, //Precedence symbol for this rule
    index: usize,         //An index number for this rule
    can_reduce: bool,   //True if this rule is ever reduced
}

#[derive(Debug)]
enum SymbolType {
    Terminal,
    NonTerminal {
        rules: Vec<WRc<RefCell<Rule>>>, //List of rules, if a NonTerminal
        first_set: RuleSet,             //First-set for all rules of this symbol
        lambda: bool,                   //True if NonTerminal and can generate an empty string
    },
    MultiTerminal(Vec<WRc<RefCell<Symbol>>>), //constituent symbols if MultiTerminal
}
use self::SymbolType::*;

#[derive(Debug)]
struct Symbol {
    name: String,               //Name of the symbol
    index: usize,               //Index number for this symbol
    typ: SymbolType,        //Either Terminal or NonTerminal
    fallback: Option<WRc<RefCell<Symbol>>>, //Fallback token in case this token desn't parse
    assoc: Option<Precedence>,  //Precedence
    use_cnt: i32,               //Number of times used
    data_type: Option<Type>,  //Data type held by this object
    dt_num: Option<usize>,      //The data type number. The .yy%d element of stack is the correct data type for this object
}

impl Symbol {
    fn is_lambda(&self) -> bool {
        match self.typ {
            NonTerminal{lambda, ..} => lambda,
            _ => false
        }
    }
}

fn symbol_cmp(a: &Rc<RefCell<Symbol>>, b: &Rc<RefCell<Symbol>>) -> Ordering {
    fn symbol_ord(s: &SymbolType) -> i32 {
        match s {
            Terminal => 0,
            NonTerminal{..} => 1,
            MultiTerminal(_) => 2,
        }
    }
    let a = symbol_ord(&a.borrow().typ);
    let b = symbol_ord(&b.borrow().typ);
    a.cmp(&b)
}

/* A configuration is a production rule of the grammar together with
* a mark (dot) showing how much of that rule has been processed so far.
* Configurations also contain a follow-set which is a list of terminal
* symbols which are allowed to immediately follow the end of the rule.
* Every configuration is recorded as an instance of the following: */
#[derive(Debug)]
enum CfgStatus {
    Complete,
    Incomplete
}

#[derive(Debug)]
struct Config {
    rule: WRc<RefCell<Rule>>,   //The rule upon which the configuration is based
    dot: usize,           //The parse point
    fws: RuleSet,       //Follow-set for this configuration only
    fplp: Vec<WRc<RefCell<Config>>>,  //Follow-set forward propagation links
    bplp: Vec<WRc<RefCell<Config>>>,  //Follow-set backwards propagation links
    status: CfgStatus,  //Used during followset and shift computations
}

fn config_cmp_key(a: &Rc<RefCell<Config>>, index: usize, dot: usize) -> Ordering {
    let adot = a.borrow().dot;
    let aindex = {
        let a2 = a.borrow().rule.upgrade();
        let ai = a2.borrow().index;
        ai
    };
    (aindex, adot).cmp(&(index, dot))
}

fn config_cmp(a: &Rc<RefCell<Config>>, b: &Rc<RefCell<Config>>) -> Ordering {
    let bdot = b.borrow().dot;
    let bindex = {
        let b2 = b.borrow().rule.upgrade();
        let bi = b2.borrow().index;
        bi
    };
    config_cmp_key(a, bindex, bdot)
}

type ConfigList = Vec<Rc<RefCell<Config>>>;

#[derive(Debug)]
enum EAction {
    Shift(WRc<RefCell<State>>),
    Accept,
    Reduce(WRc<RefCell<Rule>>),
    Error,
    SSConflict(WRc<RefCell<State>>),    //A shift/shift conflict
    SRConflict(WRc<RefCell<Rule>>),     //Was a reduce, but part of a conflict
    RRConflict(WRc<RefCell<Rule>>),     //Was a reduce, but part of a conflict
    SHResolved(WRc<RefCell<State>>),    //Was a shift. Associativity resolved conflict
    RDResolved(WRc<RefCell<Rule>>),     //Was reduce. Associativity resolved conflict
    NotUsed                             //Deleted by compression
}

fn eaction_cmp(a: &EAction, b: &EAction) -> Ordering {
    use self::EAction::*;

    match a {
        Shift(ref sa) => match b {
            Shift(ref sb) => {
                let sa = sa.upgrade();
                let sb = sb.upgrade();
                let rc = sa.borrow().state_num.cmp(&sb.borrow().state_num);
                rc
            }
            _ => Ordering::Less,
        }
        Accept => match b {
            Shift(_) => Ordering::Greater,
            Accept => Ordering::Equal,
            _ => Ordering::Less,
        }
        Reduce(ref ra) => match b {
            Shift(_) => Ordering::Greater,
            Accept => Ordering::Greater,
            Reduce(ref rb) => {
                let ra = ra.upgrade();
                let rb = rb.upgrade();
                let rc = ra.borrow().index.cmp(&rb.borrow().index);
                rc
            }
            _ => Ordering::Less,
        }
        _ => {
            Ordering::Equal
        }
    }
}

//Every shift or reduce operation is stored as one of the following
#[derive(Debug)]
struct Action {
  sp: WRc<RefCell<Symbol>>,           //The look-ahead symbol
  x: EAction,
}

fn action_cmp(a: &RefCell<Action>, b: &RefCell<Action>) -> Ordering {
    let asp = a.borrow().sp.upgrade();
    let bsp = b.borrow().sp.upgrade();
    let rc = asp.borrow().index.cmp(&bsp.borrow().index);
    match rc {
        Ordering::Equal => match eaction_cmp(&a.borrow().x, &b.borrow().x) {
            Ordering::Equal => {
                (&*a.borrow() as *const Action).cmp(&(&*b.borrow() as *const Action))
            }
            rc => rc,
        }
        rc => rc,
    }
}

#[derive(Debug)]
struct State {
    cfp: Vec<Rc<RefCell<Config>>>, //All configurations in this set
    bp: Vec<WRc<RefCell<Config>>>, //The basis configuration for this state
    state_num: usize,     //Sequential number for this state
    ap: Vec<RefCell<Action>>,    //Array of actions for this state
    n_tkn_act: i32,     //number of actions on terminals and non-terminals
    n_nt_act: i32,
    i_tkn_ofst: Option<i32>,    //yy_action[] offset for terminals and non-terminals
    i_nt_ofst: Option<i32>,
    i_dflt: usize,        //Default action
}

#[derive(Debug)]
pub struct Lemon {
    token_enum: Option<ItemEnum>,       //The enum Token{}, if specified with %token
    states: Vec<Rc<RefCell<State>>>,     //Table of states sorted by state number
    rules: Vec<Rc<RefCell<Rule>>>,        //List of all rules
    nsymbol: usize,
    nterminal: usize,
    symbols: Vec<Rc<RefCell<Symbol>>>,   //Sorted array of symbols
    err_sym: WRc<RefCell<Symbol>>,      //The error symbol
    wildcard: Option<WRc<RefCell<Symbol>>>,     //The symbol that matches anything
    arg: Option<Type>,        //Declaration of the extra argument to parser
    nconflict: i32,             //Number of parsing conflicts
    has_fallback: bool,         //True if any %fallback is seen in the grammar
    var_type: Option<Type>,
    start: Option<String>,
}

struct ParserData {
    precedence: i32,
}

#[derive(Debug)]
struct AxSet {
    stp: Rc<RefCell<State>>,    // A pointer to a state
    is_tkn: bool,               // true for tokens, false for non-terminals
    n_action: i32,              // Number of actions
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
    lookahead: usize,     // Value of the lookahead token
    action: usize,        // Action to take on the given lookahead
}

#[derive(Debug)]
struct ActionSet {
    a_lookahead: Vec<LookaheadAction>,  // A single new transaction set
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
    a_action: Vec<Option<LookaheadAction>>,     // The yy_action[] table under construction
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
            if a.lookahead != min_lookahead { continue }
            if a.action != min_action { continue }

            for jla in &at2.a_lookahead {
                let k = jla.lookahead as i32 - min_lookahead as i32 + i as i32;
                if k < 0 || k as usize >= self.a_action.len() { continue 'la }
                match self.a_action[k as usize] {
                    Some(ka) => {
                        if jla.lookahead != ka.lookahead { continue 'la }
                        if jla.action != ka.action { continue 'la }
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
                break;  /* An exact match is found at offset i */
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
                let mut r = None; //self.a_action.len();
           'ia: for i in 0 .. self.a_action.len() + max_lookahead {
                    for jla in &at2.a_lookahead {
                        let k = jla.lookahead - min_lookahead + i;
                        match self.a_action.get(k) {
                            Some(Some(_)) => { continue 'ia }
                            _ => { },
                        }
                    }
                    for (j, ja) in self.a_action.iter().enumerate() {
                        let ja = match ja {
                            None => { continue },
                            Some(ja) => ja.lookahead as i32,
                        };
                        if ja == (j as i32 + min_lookahead as i32 - i as i32) { continue 'ia }
                    }
                    r = Some(i);
                    //println!("hole at {}", i);
                    break
                }
                r.unwrap()
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
        println!();

        print!("AC:");
        for (j, ja) in self.a_action.iter().enumerate() {
            match ja {
                None => {
                    print!(" {}:-----", j);
                }
                Some(ref ja) => {
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

fn minimum_size_type(signed: bool, max: usize) -> Ident {
    if signed {
        if max < 0x80 {
            parse_quote!(i8)
        } else if max < 0x8000 {
            parse_quote!(i16)
        } else {
            parse_quote!(i32)
        }
    } else {
        if max < 0x100 {
            parse_quote!(u8)
        } else if max < 0x10000 {
            parse_quote!(u16)
        } else {
            parse_quote!(u32)
        }
    }
}

fn error<T>(msg: &'static str) -> io::Result<T> {
    Err(io::Error::new(io::ErrorKind::InvalidInput, msg))
}

fn is_uppercase(id: &Ident) -> bool {
    id.to_string().chars().next().unwrap().is_ascii_uppercase()
}

fn is_lowercase(id: &Ident) -> bool {
    id.to_string().chars().next().unwrap().is_ascii_lowercase()
}

fn generate_const<T, D>(src: &mut TokenStream, name: &str, ty: T, value: D)
where T: fmt::Display,
      D: fmt::Display {

    let txt = format!("const {}: {} = {};", name, ty, value);
    let expr : syn::ItemConst = syn::parse_str(&txt).unwrap();
    expr.to_tokens(src);
}

fn generate_array<T, D, DI>(src: &mut TokenStream, name: &str, ty: T, data: D)
where T: fmt::Display,
      DI: fmt::Display,
      D: IntoIterator<Item = DI> {
    let data = data.into_iter().collect::<Vec<_>>();
    let mut txt = format!("static {}: [{}; {}] = [", name, ty, data.len());
    for x in data{
        txt += &format!("{},", x);
    }
    txt += "];";
    let expr : syn::ItemStatic = syn::parse_str(&txt).unwrap();
    expr.to_tokens(src);
}

impl Lemon {
    pub fn new_from_decls(decls: Vec<Decl>) -> io::Result<Lemon> {
        let mut symbols = Vec::new();

        Lemon::symbol_new(&mut symbols, "$", NewSymbolType::Terminal);
        let err_sym = Lemon::symbol_new(&mut symbols, "error", NewSymbolType::NonTerminal);

        let mut lem = Lemon {
            token_enum: None,
            states: Vec::new(),
            rules: Vec::new(),
            nsymbol: 0,
            nterminal: 0,
            symbols,
            err_sym,
            wildcard: None,
            arg: None,
            nconflict: 0,
            has_fallback: false,

            var_type: None,
            start: None,
        };

        let mut pdata = ParserData {
            precedence: 0,
        };

        for decl in decls.into_iter() {
            lem.parse_one_decl(&mut pdata, decl)?;
        }

        Lemon::symbol_new(&mut lem.symbols, "{default}", NewSymbolType::NonTerminal);
        Ok(lem)
    }
    pub fn build(&mut self) -> io::Result<TokenStream> {
        self.prepare();
        self.find_rule_precedences();
        self.find_first_sets();
        self.find_states()?;
        self.find_links();
        self.find_follow_sets();
        self.find_actions()?;

        if self.nconflict > 0 {
            self.report_output();
            return error("Parsing conflicts");
        }

        self.compress_tables();
        self.resort_states();

        let src = self.generate_source()?;

        //println!("{:?}", self);
        //println!("nsymbol={}, nterminal={}", self.nsymbol, self.nterminal);
        Ok(src)
    }

    pub fn prepare(&mut self) {
        //keep $ at 0
        self.symbols[1..].sort_by(symbol_cmp);

        for (i,s) in self.symbols.iter().enumerate() {
            s.borrow_mut().index = i;
            match s.borrow().typ {
                Terminal => {
                    self.nterminal = i;
                }
                NonTerminal{..} => {
                    self.nsymbol = i;
                }
                MultiTerminal(_) => {
                }
            }
        }
        self.nterminal += 1;
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
            let mut rp = rp.borrow_mut();
            if rp.prec_sym.is_some() {
                continue;
            }

            let mut prec_sym = None;
       'ps: for (sp,_) in rp.rhs.iter() {
                let sp = sp.upgrade();
                let b = sp.borrow();
                match b.typ {
                    MultiTerminal(ref sub_sym) => {
                        for msp in sub_sym {
                            let msp = msp.upgrade();
                            if msp.borrow().assoc.is_some() {
                                prec_sym = Some(sp.clone());
                                break 'ps;
                            }
                        }
                    }
                    _ if b.assoc.is_some() => {
                        prec_sym = Some(sp.clone());
                        break 'ps;
                    }
                    _ => {}
                }
            }
            if let Some(ps) = prec_sym {
                rp.prec_sym = Some(ps.into());
            }
        }
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
                let rp = rp.borrow();
                let lhs = rp.lhs.upgrade();
                if lhs.borrow().is_lambda() { continue }

                let mut all_lambda = true;
                for (sp, _) in &rp.rhs {
                    let sp = sp.upgrade();
                    let sp = sp.borrow();
                    if !sp.is_lambda() {
                        all_lambda = false;
                        break;
                    }
                }
                if all_lambda {
                    if let NonTerminal{ ref mut lambda, ..} = lhs.borrow_mut().typ {
                        *lambda = true;
                        progress = true;
                    } else {
                        assert!(false); //Only NonTerminals have lambda
                    }
                }
            }
            if !progress { break }
        }
        //Now compute all first sets
        loop {
            let mut progress = false;

            for rp in &self.rules {
                let rp = rp.borrow();
                let s1 = rp.lhs.upgrade();
                for (s2, _) in &rp.rhs {
                    let s2 = s2.upgrade();

                    //First check if s1 and s2 are the same, or else s1.borrow_mut() will panic
                    if Rc::ptr_eq(&s1, &s2) {
                        if !s1.borrow().is_lambda() { break }
                        continue;
                    }

                    let b2 = s2.borrow();
                    if let NonTerminal{ first_set: ref mut s1_first_set, .. } = s1.borrow_mut().typ {
                        match b2.typ {
                            Terminal => {
                                progress |= s1_first_set.insert(b2.index);
                                break;
                            }
                            MultiTerminal(ref sub_sym) => {
                                for ss in sub_sym {
                                    let ss = ss.upgrade();
                                    progress |= s1_first_set.insert(ss.borrow().index);
                                }
                                break;
                            }
                            NonTerminal{ first_set: ref s2_first_set, lambda: b2_lambda, .. } => {
                                let n1 = s1_first_set.len();
                                s1_first_set.append(&mut s2_first_set.clone());
                                progress |= s1_first_set.len() > n1;
                                if !b2_lambda { break }
                            }
                        }
                    }
                }
            }
            if !progress { break }
        }
    }

    /* Compute all LR(0) states for the grammar.  Links
     ** are added to between some states so that the LR(1) follow sets
     ** can be computed later.
     */
    fn find_states(&mut self) -> io::Result<()> {
        /* Find the start symbol */
        let sp = match self.start {
            None => {
                let r = self.rules.first().unwrap();
                let b = r.borrow();
                b.lhs.upgrade();

                self.rules.first().unwrap().borrow().lhs.upgrade()
            }
            Some(ref s) => {
                match self.symbol_find(s) {
                    Some(x) => x,
                    None => return error("start with unknown symbol"),
                }
            }
        };

        /* Make sure the start symbol doesn't occur on the right-hand side of
         ** any rule.  Report an error if it does.  (YACC would generate a new
         ** start symbol in this case.) */
        for rp in &self.rules {
            let rp = rp.borrow_mut();
            for (r,_) in &rp.rhs {
                let r = r.upgrade();
                if Rc::ptr_eq(&sp, &r) {
                    return error("start symbol on the RHS of a rule");
                }
                let r = r.borrow();
                if let MultiTerminal(ref sub_sym) = r.typ {
                    for r2 in sub_sym {
                        let r2 = r2.upgrade();
                        if Rc::ptr_eq(&sp, &r2) {
                            return error("start symbol on the RHS of a rule");
                        }
                    }
                }
            }
        }

        let mut basis = ConfigList::new();

        /* The basis configuration set for the first state
         ** is all rules which have the start symbol as their
         ** left-hand side */
        if let NonTerminal{ref rules, ..} = sp.borrow().typ {
            for rp in rules {
                let rp = rp.upgrade();
                rp.borrow_mut().lhs_start = true;

                let cfg = Lemon::add_config(&mut basis, rp, 0);
                cfg.borrow_mut().fws.insert(0);
            }
        }
        self.get_state(basis.clone(), basis)?;

        Ok(())
    }

    /* Compute the first state.  All other states will be
     ** computed automatically during the computation of the first one.
     ** The returned pointer to the first state is not used. */
    fn get_state(&mut self, mut bp: ConfigList, cur: ConfigList) -> io::Result<Rc<RefCell<State>>> {
        bp.sort_by(config_cmp);
        /* Get a state with the same basis */
        match self.state_find(&bp) {
            Some(stp) => {
                /* A state with the same basis already exists!  Copy all the follow-set
                 ** propagation links from the state under construction into the
                 ** preexisting state, then return a pointer to the preexisting state */
                let bstp = stp.borrow();
                for (x, y) in bp.into_iter().zip(&bstp.bp) {
                    let y = y.upgrade();
                    let mut y = y.borrow_mut();
                    y.bplp.extend(x.borrow_mut().bplp.iter().map(|x| x.clone()));
                }
                Ok(stp.clone())
            }
            None => {
                /* This really is a new state. Construct all the details */
                let mut cfp = self.configlist_closure(cur)?;
                cfp.sort_by(config_cmp);
                let stp = Rc::new(RefCell::new(State {
                    cfp: cfp,
                    bp: bp.iter().map(WRc::from).collect(),
                    state_num: self.states.len(),
                    ap: Vec::new(),
                    n_tkn_act: 0,
                    n_nt_act: 0,
                    i_tkn_ofst: None,
                    i_nt_ofst: None,
                    i_dflt: 0,
                }));
                self.states.push(stp.clone());
                self.build_shifts(&stp)?;
                Ok(stp)
            }
        }
    }
    /* Construct all successor states to the given state.  A "successor"
     ** state is any state which can be reached by a shift action.
     */
    fn build_shifts(&mut self, state: &Rc<RefCell<State>>) -> io::Result<()> {
        /* Each configuration becomes complete after it contibutes to a successor
         ** state.  Initially, all configurations are incomplete */

        for cfp in &state.borrow().cfp {
            cfp.borrow_mut().status = CfgStatus::Incomplete;
        }
        let mut aps = Vec::new();
        /* Loop through all configurations of the state "stp" */
        for (icfp, cfp) in state.borrow().cfp.iter().enumerate() {
            let cfp = cfp.borrow();
            if let CfgStatus::Complete = cfp.status { continue }/* Already used by inner loop */
            let rule = cfp.rule.upgrade();
            if cfp.dot >= rule.borrow().rhs.len() { continue }  /* Can't shift this config */
            let (ref sp, _) = rule.borrow().rhs[cfp.dot];       /* Symbol after the dot */
            let sp = sp.upgrade();
            let mut basis = ConfigList::new();
            drop(cfp);

            /* For every configuration in the state "stp" which has the symbol "sp"
             ** following its dot, add the same configuration to the basis set under
             ** construction but with the dot shifted one symbol to the right. */
            for bcfp_ in &state.borrow().cfp[icfp..] {
                let bcfp = bcfp_.borrow();
                if let CfgStatus::Complete = bcfp.status { continue }   /* Already used */
                let brule = bcfp.rule.upgrade();
                if bcfp.dot >= brule.borrow().rhs.len() { continue }    /* Can't shift this one */
                let (ref bsp, _) = brule.borrow().rhs[bcfp.dot];        /* Get symbol after dot */
                let bsp = bsp.upgrade();
                if !Rc::ptr_eq(&bsp, &sp) { continue }                     /* Must be same as for "cfp" */
                let newcfg = Lemon::add_config(&mut basis, brule.clone(), bcfp.dot + 1);
                drop(bcfp);

                bcfp_.borrow_mut().status = CfgStatus::Complete;                      /* Mark this config as used */
                newcfg.borrow_mut().bplp.push(bcfp_.into());
            }

            /* Get a pointer to the state described by the basis configuration set
             ** constructed in the preceding loop */
            let newstp = self.get_state(basis.clone(), basis)?;

            /* The state "newstp" is reached from the state "stp" by a shift action
             ** on the symbol "sp" */
            let bsp = sp.borrow();
            match bsp.typ {
                MultiTerminal(ref sub_sym) => {
                    for ss in sub_sym {
                        let x = EAction::Shift((&newstp).into());
                        aps.push(RefCell::new(Action {
                            sp: ss.clone(),
                            x
                        }));
                    }
                }
                _ => {
                    let x = EAction::Shift((&newstp).into());
                    aps.push(RefCell::new(Action {
                        sp: (&sp).into(),
                        x
                    }));
                }
            }
        }
        state.borrow_mut().ap.extend(aps);

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
            for cfp in &stp.borrow().cfp {
                for plp in &cfp.borrow().bplp {
                    let plp = plp.upgrade();
                    plp.borrow_mut().fplp.push(cfp.into());
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
            for cfp in &stp.borrow().cfp {
                cfp.borrow_mut().status = CfgStatus::Incomplete;
            }
        }

        let mut progress = true;
        while progress {
            progress = false;
            for stp in &self.states {
                for cfp in &stp.borrow().cfp {
                    let mut cfp = cfp.borrow_mut();
                    match cfp.status {
                        CfgStatus::Complete => (),
                        CfgStatus::Incomplete => {
                            for plp in &cfp.fplp {
                                let mut fws = cfp.fws.clone();

                                let plp = plp.upgrade();
                                let mut plp = plp.borrow_mut();
                                let n = plp.fws.len();
                                plp.fws.append(&mut fws);
                                if plp.fws.len() > n {
                                    plp.status = CfgStatus::Incomplete;
                                    progress = true;
                                }
                            }
                            cfp.status = CfgStatus::Complete;
                        }
                    }
                }
            }
        }
    }

    /* Compute the reduce actions, and resolve conflicts.
    */
    fn find_actions(&mut self) -> io::Result<()> {
        /* Add all of the reduce actions
         ** A reduce action is added for each element of the followset of
         ** a configuration which has its dot at the extreme right.
         */
        for stp in &self.states {
            let mut aps = Vec::new();
            let mut stp = stp.borrow_mut();
            for cfp in &stp.cfp {
                let mut cfp = cfp.borrow_mut();
                let rule = cfp.rule.upgrade();
                if cfp.dot == rule.borrow().rhs.len() { /* Is dot at extreme right? */
                    for j in 0 .. self.nterminal {
                        if cfp.fws.contains(&j) {
                            /* Add a reduce action to the state "stp" which will reduce by the
                             ** rule "cfp->rp" if the lookahead symbol is "lemp->symbols[j]" */
                            let x = EAction::Reduce((&rule).into());
                            aps.push(RefCell::new(Action {
                                sp: (&self.symbols[j]).into(),
                                x
                            }));
                        }
                    }
                }
            }
            stp.ap.extend(aps);
        }

        /* Add the accepting token */
        let sp = match self.start {
            Some(ref start) => self.symbol_find(&start).unwrap(),
            None => self.rules.first().unwrap().borrow().lhs.upgrade(),
        };

        /* Add to the first state (which is always the starting state of the
         ** finite state machine) an action to ACCEPT if the lookahead is the
         ** start nonterminal.  */
        self.states.first().unwrap().borrow_mut().ap.push(RefCell::new(Action {
            sp: sp.into(),
            x: EAction::Accept,
        }));

        /* Resolve conflicts */
        for stp in &self.states {
            stp.borrow_mut().ap.sort_by(action_cmp);
            let stp = stp.borrow();
            let len = stp.ap.len();
            for i in 0 .. len {
                let ref ap = stp.ap[i];
                for j in i + 1 .. len {
                    let ref nap = stp.ap[j];
                    if Rc::ptr_eq(&ap.borrow().sp.upgrade(), &nap.borrow().sp.upgrade()) {
                        /* The two actions "ap" and "nap" have the same lookahead.
                         ** Figure out which one should be used */
                        self.nconflict += if Lemon::resolve_conflict(&mut *ap.borrow_mut(), &mut *nap.borrow_mut()) { 1 } else { 0 };
                    } else {
                        break;
                    }
                }
            }
        }


        /* Report an error for each rule that can never be reduced. */
        for stp in &self.states {
            for a in &stp.borrow().ap {
                let a = a.borrow();
                if let EAction::Reduce(ref x) = a.x {
                    let x = x.upgrade();
                    x.borrow_mut().can_reduce = true;
                }
            }
        }
        for rp in &self.rules {
            if !rp.borrow().can_reduce {
                return error("This rule cannot be reduced");
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
    fn resolve_conflict(apx: &mut Action, apy: &mut Action) -> bool {
        use self::EAction::*;
        let (err, ax, ay) = match (&mut apx.x, &mut apy.x) {
            (Shift(x), Shift(y)) => {
                (true, Shift(x.clone()), SSConflict(y.clone()))
            }
            /* Use operator associativity to break tie */
            (Shift(x), Reduce(y)) => {
                let spx = apx.sp.upgrade();
                let ry = y.upgrade();
                let ref spy = ry.borrow().prec_sym;
                let precx = spx.borrow().assoc;
                let precy = Lemon::get_precedence(&spy);

                match (precx, precy) {
                    (Some(px), Some(py)) => {
                        match precedence_cmp(&px, &py) {
                            Ordering::Less => (false, SHResolved(x.clone()), Reduce(y.clone())),
                            Ordering::Equal => (false, Error, Reduce(y.clone())),
                            Ordering::Greater => (false, Shift(x.clone()), RDResolved(y.clone())),
                        }
                    }
                    _ => (true, Shift(x.clone()), SRConflict(y.clone()))
                }
            }
            (Reduce(x), Reduce(y)) => {
                let rx = x.upgrade();
                let ry = y.upgrade();
                let ref spx = rx.borrow().prec_sym;
                let ref spy = ry.borrow().prec_sym;
                let precx = Lemon::get_precedence(&spx);
                let precy = Lemon::get_precedence(&spy);

                match (precx, precy) {
                    (Some(px), Some(py)) => {
                        match precedence_cmp(&px, &py) {
                            Ordering::Less => (false, RDResolved(x.clone()), Reduce(y.clone())),
                            Ordering::Equal => (true, Reduce(x.clone()), RRConflict(y.clone())),
                            Ordering::Greater => (false, Reduce(x.clone()), RDResolved(y.clone())),
                        }
                    }
                    _ => (true, Reduce(x.clone()), RRConflict(y.clone()))
                }
            }
            /* The REDUCE/SHIFT case cannot happen because SHIFTs come before
             ** REDUCEs on the list.  If we reach this point it must be because
             ** the parser conflict had already been resolved. */
            _ => return false,
        };
        apx.x = ax;
        apy.x = ay;
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
        let def_symbol = self.symbol_find("{default}").unwrap();

        for stp in &self.states {
            {
                let mut nbest = 0;
                let mut rbest = None;
                let mut uses_wildcard = false;
                let stp = stp.borrow();
                for (iap, ap) in stp.ap.iter().enumerate() {
                    let ap = ap.borrow();
                    match (&ap.x, &self.wildcard) {
                        (EAction::Shift(_), Some(w)) => {
                            let sp = ap.sp.upgrade();
                            let w = w.upgrade();
                            if Rc::ptr_eq(&sp, &w) {
                                uses_wildcard = true;
                            }
                        }
                        (EAction::Reduce(ref rp), _) => {
                            let rp = rp.upgrade();
                            if rp.borrow().lhs_start { continue }
                            if let Some(ref rbest) = rbest {
                                if Rc::ptr_eq(&rp, &rbest) { continue }
                            }
                            let mut n = 1;
                            for ap2 in &stp.ap[iap + 1..] {
                                let ap2 = ap2.borrow();
                                match &ap2.x {
                                    EAction::Reduce(ref rp2) => {
                                        let rp2 = rp2.upgrade();
                                        if let Some(ref rbest) = rbest {
                                            if Rc::ptr_eq(&rp2, &rbest) { continue }
                                        }
                                        if Rc::ptr_eq(&rp2, &rp) {
                                            n += 1;
                                        }
                                    }
                                    _ => continue
                                }
                            }
                            if n > nbest {
                                nbest = n;
                                rbest = Some(rp);
                            }
                        }
                        _ => continue,
                    }
                }

                /* Do not make a default if the number of rules to default
                 ** is not at least 1 or if the wildcard token is a possible
                 ** lookahead.
                 */
                if nbest < 1 || uses_wildcard { continue }
                let rbest = rbest.unwrap();

                /* Combine matching REDUCE actions into a single default */

                let mut apbest = None;
                for (iap, ap) in stp.ap.iter().enumerate() {
                    let bap = ap.borrow();
                    match &bap.x {
                        EAction::Reduce(ref rp) => {
                            let rp = rp.upgrade();
                            if Rc::ptr_eq(&rp, &rbest) {
                                apbest = Some((iap, ap));
                                break;
                            }
                        }
                        _ => ()
                    }
                }
                if let Some((iap, ap)) = apbest {
                    ap.borrow_mut().sp = (&def_symbol).into();
                    for ap2 in &stp.ap[iap + 1..] {
                        let mut ap2 = ap2.borrow_mut();
                        let unuse = match &ap2.x {
                            EAction::Reduce(ref rp) => {
                                let rp = rp.upgrade();
                                Rc::ptr_eq(&rp, &rbest)
                            }
                            _ => false
                        };
                        if unuse {
                            ap2.x = EAction::NotUsed;
                        }
                    }
                }
            }
            stp.borrow_mut().ap.sort_by(action_cmp);
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

            for ap in &stp.borrow().ap {
                let ap = ap.borrow();
                match self.compute_action(&ap) {
                    Some(x) => {
                        let sp = ap.sp.upgrade();
                        let index = sp.borrow().index;
                        if index < self.nterminal {
                            n_tkn_act += 1;
                        } else if index < self.nsymbol {
                            n_nt_act += 1;
                        } else {
                            i_dflt = x;
                        }
                    }
                    None => ()
                }
            }

            let mut stp = stp.borrow_mut();
            stp.n_tkn_act = n_tkn_act;
            stp.n_nt_act = n_nt_act;
            stp.i_dflt = i_dflt;
        }
        self.states[1..].sort_by(Lemon::state_resort_cmp);
        for (i, stp) in self.states.iter().enumerate() {
            stp.borrow_mut().state_num = i;
        }
    }

    /* Given an action, compute the integer value for that action
     ** which is to be put in the action table of the generated machine.
     ** Return None if no action should be generated.
     */
    fn compute_action(&self, ap: &Action) -> Option<usize> {
        use self::EAction::*;
        let act = match &ap.x {
            Shift(ref stp) => {
                let stp = stp.upgrade();
                let n = stp.borrow().state_num;
                n
            }
            Reduce(ref rp) => {
                let rp = rp.upgrade();
                let n = rp.borrow().index + self.states.len();
                n
            }
            Error => self.states.len() + self.rules.len(),
            Accept => self.states.len() + self.rules.len() + 1,
            _ => return None,
        };
        Some(act)
    }

    fn report_output(&self) {
        for stp in &self.states {
            let stp = stp.borrow();
            let mut state_info = format!("State {}:\n", stp.state_num);
            let mut num_conflicts = 0;
            for cfp in &stp.cfp {
                let cfp = cfp.borrow();
                let rule = cfp.rule.upgrade();
                let rule = rule.borrow();
                if cfp.dot == rule.rhs.len() {
                    state_info += &format!("    {:>5} ", format!("({})", rule.index));
                } else {
                    state_info += &format!("          ");
                }
                let lhs = rule.lhs.upgrade();
                state_info += &format!("{} ::=", lhs.borrow().name);
                for (i, (sp,_)) in rule.rhs.iter().enumerate() {
                    if i == cfp.dot {
                        state_info += &format!(" *");
                    }
                    let sp = sp.upgrade();
                    let sp = sp.borrow();
                    if let MultiTerminal(ref sub_sym) = sp.typ {
                        for (j, ss) in sub_sym.iter().enumerate() {
                            let ss = ss.upgrade();
                            let ss = ss.borrow();
                            if j == 0 {
                                state_info += &format!(" {}", ss.name);
                            } else {
                                state_info += &format!("|{}", ss.name);
                            }
                        }
                    } else {
                        state_info += &format!(" {}", sp.name);
                    }
                }
                if cfp.dot == rule.rhs.len() {
                    state_info += &format!(" *");
                }
                state_info += "\n";
            }
            state_info += "\n";
            for ap in &stp.ap {
                let ap = ap.borrow();
                use self::EAction::*;
                let sp = ap.sp.upgrade();
                let sp = sp.borrow();
                match ap.x {
                    Shift(ref stp) => {
                        let stp = stp.upgrade();
                        let stp = stp.borrow();
                        state_info += &format!("{:>30} shift  {}", sp.name, stp.state_num);
                    }
                    Reduce(ref rp) => {
                        let rp = rp.upgrade();
                        let rp = rp.borrow();
                        state_info += &format!("{:>30} reduce {}", sp.name, rp.index);
                    }
                    Accept => {
                        state_info += &format!("{:>30} accept", sp.name);
                    }
                    Error => {
                        state_info += &format!("{:>30} error", sp.name);
                    }
                    SRConflict(ref rp) |
                    RRConflict(ref rp) => {
                        let rp = rp.upgrade();
                        let rp = rp.borrow();
                        state_info += &format!("{:>30} reduce {:<3} ** Parsing conflict **", sp.name, rp.index);
                        num_conflicts += 1;
                    }
                    SSConflict(ref stp) => {
                        let stp = stp.upgrade();
                        let stp = stp.borrow();
                        state_info += &format!("{:>30} shift  {:<3} ** Parsing conflict **", sp.name, stp.state_num);
                        num_conflicts += 1;
                    }
                    SHResolved(ref stp) => {
                        let stp = stp.upgrade();
                        let stp = stp.borrow();
                        state_info += &format!("{:>30} shift  {:<3} -- dropped by precedence", sp.name, stp.state_num);
                    }
                    RDResolved(ref rp) => {
                        let rp = rp.upgrade();
                        let rp = rp.borrow();
                        state_info += &format!("{:>30} reduce {:<3} -- dropped by precedence", sp.name, rp.index);
                    }
                    _ => continue,
                }
                state_info += "\n";
            }
            state_info += "\n";
            if num_conflicts > 0 {
                print!("{}", state_info);
            }
        }
        /*
        println!("----------------------------------------------------");
        println!("Symbols:");
        for i in 0 .. self.nsymbol {
            let sp = self.symbols[i].borrow();
            print!("  {:3}: {}", i, sp.name);
            if let NonTerminal{ref first_set, lambda, ..} = sp.typ {
                print!(":");
                if lambda {
                    print!(" <lambda>");
                }
                for j in 0 .. self.nterminal {
                    if first_set.contains(&j) {
                        print!(" {}", self.symbols[j].borrow().name);
                    }
                }
            }
            println!();
        }*/
    }

    fn get_precedence(p: &Option<WRc<RefCell<Symbol>>>) -> Option<Precedence> {
        p.as_ref().and_then(|y| {
            let y = y.upgrade();
            let y = y.borrow();
            y.assoc
        })
    }

    fn state_find(&mut self, bp: &ConfigList) -> Option<Rc<RefCell<State>>> {
        let res = self.states.iter().find(|s| {
            let ref sbp = s.borrow().bp;
            if sbp.len() != bp.len() {
                return false;
            }
            for (a, b) in sbp.iter().zip(bp) {
                let a = a.upgrade();
                let a = a.borrow();
                let b = b.borrow();
                if !Rc::ptr_eq(&a.rule.upgrade(), &b.rule.upgrade()) ||
                    a.dot != b.dot {
                    return false;
                }
            }
            true
        });
        res.map(|x| x.clone())
    }

    /* Compute the closure of the configuration list */
    fn configlist_closure(&mut self, mut cur: ConfigList) -> io::Result<ConfigList> {
        let mut i = 0;
        while i < cur.len() {
            //println!("I = {} < {}", i, cur.len());
            let cfp = cur[i].clone();
            let rp = cfp.borrow().rule.upgrade();
            let ref rhs = rp.borrow().rhs;
            let dot = cfp.borrow().dot;
            if dot < rhs.len() {
                let sp = rhs[dot].0.upgrade();
                let ref spt = sp.borrow().typ;
                if let NonTerminal{ref rules, ..} = spt {
                    if rules.is_empty() {
                        let is_err_sym = Rc::ptr_eq(&sp, &self.err_sym.upgrade());
                        if !is_err_sym {
                            return error("Nonterminal has no rules");
                        }
                    }
                    for newrp in rules {
                        let newcfp = Lemon::add_config(&mut cur, newrp.upgrade(), 0);
                        let mut broken = false;
                        for xsp in &rhs[dot + 1 ..] {
                            let xsp = xsp.0.upgrade();
                            let xsp = xsp.borrow();
                            match xsp.typ {
                                Terminal => {
                                    newcfp.borrow_mut().fws.insert(xsp.index);
                                    broken = true;
                                    break;
                                }
                                MultiTerminal(ref sub_sym) => {
                                    let mut bn = newcfp.borrow_mut();
                                    for k in sub_sym {
                                        let k = k.upgrade();
                                        bn.fws.insert(k.borrow().index);
                                    }
                                    broken = true;
                                    break;
                                }
                                NonTerminal{ ref first_set, lambda, ..} => {
                                    newcfp.borrow_mut().fws.append(&mut first_set.clone());
                                    if lambda {
                                        broken = true;
                                        break;
                                    }
                                }
                            }
                        }
                        if !broken {
                            cfp.borrow_mut().fplp.push((&newcfp).into());
                        }
                    }
                }
            }
            i += 1;
        }

        Ok(cur)
    }

    fn add_config(cfgs: &mut ConfigList, rp: Rc<RefCell<Rule>>, dot: usize) -> Rc<RefCell<Config>> {
        match cfgs.iter().position(|x| config_cmp_key(x, rp.borrow().index, dot) == Ordering::Equal) {
            Some(i) => cfgs[i].clone(),
            None => {
                let c = Rc::new(RefCell::new(Config {
                    rule: rp.into(),
                    dot,
                    fws: RuleSet::new(),
                    fplp: Vec::new(),
                    bplp: Vec::new(),
                    //stp: None,
                    status: CfgStatus::Incomplete,
                }));
                cfgs.push(c.clone());
                c
            }
        }
    }

    fn symbol_new_b(&mut self, name: &[u8], typ: NewSymbolType) -> WRc<RefCell<Symbol>> {
        Lemon::symbol_new(&mut self.symbols, String::from_utf8_lossy(name).as_ref(), typ)
    }
    fn symbol_new_t(&mut self, name: &Ident, typ: NewSymbolType) -> WRc<RefCell<Symbol>> {
        Lemon::symbol_new(&mut self.symbols, name.to_string().as_ref(), typ)
    }
    fn symbol_new(symbols: &mut Vec<Rc<RefCell<Symbol>>>, name: &str, typ: NewSymbolType) -> WRc<RefCell<Symbol>> {
        if !name.is_empty() {
            for s in symbols.iter() {
                let mut b = s.borrow_mut();
                if b.name == name {
                    b.use_cnt += 1;
                    return s.into();
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
            NewSymbolType::MultiTerminal => MultiTerminal(Vec::new())
        };
        let symbol = Symbol {
            name: name.to_string(),
            index: 0,
            typ,
            fallback: None,
            assoc: None,
            use_cnt: 1,
            data_type: None,
            dt_num: None,
        };
        let symbol = Rc::new(RefCell::new(symbol));
        let w = (&symbol).into();
        symbols.push(symbol);
        w
    }
    fn symbol_find(&self, name: &str) -> Option<Rc<RefCell<Symbol>>> {
        for s in &self.symbols {
            let b = s.borrow();
            if b.name == name {
                return Some(s.clone());
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
    fn state_resort_cmp(a: &Rc<RefCell<State>>, b: &Rc<RefCell<State>>) -> Ordering {
        let a = a.borrow();
        let b = b.borrow();
        (b.n_nt_act, b.n_tkn_act, b.state_num).cmp(&(a.n_nt_act, a.n_tkn_act, a.state_num))
    }

    fn parse_one_decl(&mut self, pdt: &mut ParserData, decl: Decl) -> io::Result<()> {
        //println!("PARSE {:?}", decl);
        match decl {
            Decl::Type(id, ty) => {
                let nst = if is_uppercase(&id) {
                    NewSymbolType::Terminal
                } else if is_lowercase(&id) {
                    NewSymbolType::NonTerminal
                } else {
                    return error("Symbol name missing");
                };
                let sp = self.symbol_new_t(&id, nst).upgrade();
                let mut sp = sp.borrow_mut();
                if sp.data_type.is_some() {
                    return error("Symbol type already defined");
                }
                sp.data_type = Some(ty);
            }
            Decl::Assoc(a, ids) => {
                pdt.precedence += 1;
                for token in ids {
                    if !is_uppercase(&token) {
                        return error("Precedence must be assigned to a token");
                    }
                    let sp = self.symbol_new_t(&token, NewSymbolType::Terminal).upgrade();
                    let mut b = sp.borrow_mut();
                    match b.assoc {
                        Some(_) => return error("Symbol has already been given a precedence"),
                        None => b.assoc = Some(Precedence(pdt.precedence, a)),
                    }
                }
            }
            Decl::DefaultType(ty) => {
                if self.var_type.is_some() {
                    return error("Default type already defined");
                }
                self.var_type = Some(ty);
            }
            Decl::ExtraArgument(ty) => {
                if self.var_type.is_some() {
                    return error("Extra argument type already defined");
                }
                self.arg = Some(ty);
            }
            Decl::StartSymbol(id) => {
                if self.start.is_some() {
                    return error("Start symbol already defined");
                }
                self.start = Some(id.to_string());
            }
            Decl::Fallback(fb, ids) => {
                    if !is_uppercase(&fb) {
                        return error("Fallback must be a token");
                    }
                let fallback = self.symbol_new_t(&fb, NewSymbolType::Terminal);
                for id in ids {
                    if !is_uppercase(&fb) {
                        return error("Fallback must be a token");
                    }
                    let sp = self.symbol_new_t(&id, NewSymbolType::Terminal).upgrade();
                    let mut b = sp.borrow_mut();
                    if b.fallback.is_some() {
                        return error("More than one fallback assigned to token");
                    }
                    b.fallback = Some(fallback.clone());
                    self.has_fallback = true;
                }
            }
            Decl::Wildcard(id) => {
                if self.wildcard.is_some() {
                    return error("Wildcard already defined");
                }
                if !is_uppercase(&id) {
                    return error("Wildcard must be a token");
                }
                let sp = self.symbol_new_t(&id, NewSymbolType::Terminal);
                self.wildcard = Some(sp);
            }
            Decl::TokenClass(tk, ids) => {
                let tk = self.symbol_new_t(&tk, NewSymbolType::MultiTerminal).upgrade();
                if let MultiTerminal(ref mut sub_sym) = tk.borrow_mut().typ {
                    for id in ids {
                        let sp = self.symbol_new_t(&id, NewSymbolType::Terminal);
                        sub_sym.push(sp.into());
                    }
                } else {
                    unreachable!();
                };
            }
            Decl::Token(e) => {
                if self.token_enum.is_some() {
                    return error("%token redeclared");
                }
                self.token_enum = Some(e);
                //TODO
            }
            Decl::Rule{ lhs, rhs, action, prec } => {
                if !is_lowercase(&lhs) {
                    return error("LHS of rule must be non-terminal");
                }
                let lhs = self.symbol_new_t(&lhs, NewSymbolType::NonTerminal);
                let rhs = rhs.into_iter().map(|(toks, alias)| {
                    let tok = if toks.len() == 1 {
                        let tok = toks.into_iter().next().unwrap();
                        let nst = if is_uppercase(&tok) {
                            NewSymbolType::Terminal
                        } else if is_lowercase(&tok) {
                            NewSymbolType::NonTerminal
                        } else {
                            return error("Invalid token in RHS of rule");
                        };
                        self.symbol_new_t(&tok, nst)
                    } else {
                        let mt = self.symbol_new_b(b"", NewSymbolType::MultiTerminal).upgrade();
                        let mut ss = Vec::new();
                        for tok in toks {
                            if !is_uppercase(&tok) {
                                return error("Cannot form a compound containing a non-terminal");
                            }
                            ss.push(self.symbol_new_t(&tok, NewSymbolType::Terminal));
                        }
                        if let MultiTerminal(ref mut sub_sym) = mt.borrow_mut().typ {
                            sub_sym.extend(ss);
                        } else {
                            unreachable!();
                        }
                        mt.into()
                    };
                    let alias = alias.as_ref().map(|id| id.to_string());
                    Ok((tok, alias))
                }).collect::<io::Result<Vec<_>>>()?;

                let prec_sym = match prec.as_ref() {
                    Some(id) => {
                        if !is_uppercase(id) {
                            return error("The precedence symbol must be a terminal");
                        }
                        Some(self.symbol_new_t(id, NewSymbolType::Terminal))
                    }
                    None => None
                };

                let index = self.rules.len();
                let rule = Rule {
                    lhs: lhs.clone(),
                    lhs_start: false,
                    rhs,
                    code: action,
                    prec_sym,
                    index,
                    can_reduce: false,
                };
                let rule = Rc::new(RefCell::new(rule));
                let lhs = lhs.upgrade();
                if let NonTerminal{ref mut rules, ..} = lhs.borrow_mut().typ {
                    rules.push((&rule).into());
                } else {
                    unreachable!();
                }
                self.rules.push(rule);
            }
        }
        Ok(())
    }

    fn generate_source(&self) -> io::Result<TokenStream> {
        let mut src = TokenStream::new();
        src.extend(quote!{
            #![allow(dead_code)]
            #![allow(unused_variables)]
            #![allow(non_snake_case)]
        });

        /* Generate the defines */
        let yycodetype = minimum_size_type(true, self.nsymbol+1);
        let yyactiontype = minimum_size_type(false, self.states.len() + self.rules.len() + 5);
        src.extend(quote!{
            type YYCODETYPE = #yycodetype;
            type YYACTIONTYPE = #yyactiontype;
        });

        generate_const(&mut src, "YYNOCODE", "i32", self.nsymbol + 1);

        let yywildcard = if let Some(ref wildcard) = self.wildcard {
            let wildcard = wildcard.upgrade();
            let wildcard = wildcard.borrow();
            if wildcard.data_type.is_some() {
                return error("Wildcard token must not have a type");
            }
            wildcard.index
        } else {
            0
        };

        generate_const(&mut src, "YYWILDCARD", "YYCODETYPE", yywildcard);
        /*
         ** Print the definition of the union used for the parser's data stack.
         ** This union contains fields for every possible data type for tokens
         ** and nonterminals.  In the process of computing and printing this
         ** union, also set the ".dtnum" field of every terminal and nonterminal
         ** symbol.
         */
        let mut types = HashMap::new();

        for i in 0..self.nsymbol {
            let ref sp = self.symbols[i];

            if Rc::ptr_eq(&sp, &self.err_sym.upgrade()) {
                continue;
            }

            let mut sp = sp.borrow_mut();

            /* The ".dtnum" field of each symbol is filled.  A ".dtnum" value of 0 is
             ** used for terminal symbols.  If there is no %default_type defined then
             ** 0 is also used as the .dtnum value for nonterminals which do not specify
             ** a datatype using the %type directive.
             */
            if let SymbolType::MultiTerminal(_) = sp.typ {
                sp.dt_num = None;
                continue;
            }

            sp.dt_num = {
                let cp = sp.data_type.as_ref().or(self.var_type.as_ref());
                match cp {
                    None => None,
                    Some(cp) => {
                        let next = types.len() + 1;
                        Some(*types.entry(cp.clone()).or_insert(next))
                    }
                }
            };
        }

        let mut yytoken = match self.token_enum {
            Some(ref e) => e.clone(),
            None => parse_quote!{ pub enum Token{} },
        };

        if !yytoken.variants.is_empty() {
            return error("Token enum declaration must be empty");
        }

        let (yy_generics_impl, yy_generics, yy_generics_where) = yytoken.generics.split_for_impl();

        /* Print out the definition of YYTOKENTYPE and YYMINORTYPE */
        let mut yyminortype_str = format!("enum YYMinorType{} {} {{ YY0,",
                    tokens_to_string(&yy_generics_impl),
                    tokens_to_string(&yy_generics_where),
                    );
        for (k, v) in &types {
            yyminortype_str += &format!("YY{}({}),", v, tokens_to_string(&k));
        }
        yyminortype_str += "}";
        let yyminortype_enum : ItemEnum = syn::parse_str(&yyminortype_str).unwrap();
        yyminortype_enum.to_tokens(&mut src);


        generate_const(&mut src, "YYNSTATE", "i32", self.states.len());
        generate_const(&mut src, "YYNRULE", "i32", self.rules.len());

        {
            let err_sym = self.err_sym.upgrade();
            let mut err_sym = err_sym.borrow_mut();
            err_sym.dt_num = Some(types.len() + 1);

            let yyerrorsymbol = if err_sym.use_cnt > 0 {
                err_sym.index as i32
            } else {
                0
            };
            generate_const(&mut src, "YYERRORSYMBOL", "i32", yyerrorsymbol);
        }

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
                stp: stp.clone(),
                is_tkn: true,
                n_action: stp.borrow().n_tkn_act,
            });
            ax.push(AxSet {
                stp: stp.clone(),
                is_tkn: false,
                n_action: stp.borrow().n_nt_act,
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

            if a.n_action == 0 { continue }
            if a.is_tkn {
                for ap in &a.stp.borrow().ap {
                    let ap = ap.borrow();
                    let sp = ap.sp.upgrade();
                    let sp = sp.borrow();
                    if sp.index >= self.nterminal { continue }
                    match self.compute_action(&ap) {
                        None => continue,
                        Some(action) => actset.add_action(sp.index, action),
                    }
                }
                let ofs = acttab.insert_action_set(&actset);
                let mut stp = a.stp.borrow_mut();
                stp.i_tkn_ofst = Some(ofs);
                min_tkn_ofst = cmp::min(ofs, min_tkn_ofst);
                max_tkn_ofst = cmp::max(ofs, max_tkn_ofst);
            } else {
                for ap in &a.stp.borrow().ap {
                    let ap = ap.borrow();
                    let sp = ap.sp.upgrade();
                    let sp = sp.borrow();
                    if sp.index < self.nterminal { continue }
                    if sp.index == self.nsymbol { continue }
                    match self.compute_action(&ap) {
                        None => continue,
                        Some(action) => actset.add_action(sp.index, action),
                    }
                }
                let ofs = acttab.insert_action_set(&actset);
                let mut stp = a.stp.borrow_mut();
                stp.i_nt_ofst = Some(ofs);
                min_nt_ofst = cmp::min(ofs, min_nt_ofst);
                max_nt_ofst = cmp::max(ofs, max_nt_ofst);
            }
        }
        /* Output the yy_action table */
        let yytoken_span = yytoken.brace_token.0;

        for i in 1 .. self.nterminal {
            let ref s = self.symbols[i];
            let s = s.borrow();
            let dt = match s.data_type {
                Some(ref dt) => {
                    syn::Fields::Unnamed( parse_quote!{ (#dt) })
                }
                None => {
                    syn::Fields::Unit
                }
            };
            yytoken.variants.push(syn::Variant {
                attrs: vec![],
                ident: Ident::new(&s.name, yytoken_span),
                fields: dt,
                discriminant: None,
            });
        }
        yytoken.to_tokens(&mut src);

        let mut yytoken_str = format!("
            #[inline]
            fn token_value{0}(t: Token{1}) -> (i32, YYMinorType{1}) {2} {{
                match t {{ ",
                tokens_to_string(&yy_generics_impl),
                tokens_to_string(&yy_generics),
                tokens_to_string(&yy_generics_where));
        for i in 1 .. self.nterminal {
            let s = self.symbols[i].borrow();
            match s.dt_num {
                Some(dt) => {
                    yytoken_str += &format!("Token::{}(x) => ({}, YYMinorType::YY{}(x)),", s.name, i, dt);
                }
                None => {
                    yytoken_str += &format!("Token::{} => ({}, YYMinorType::YY0),", s.name, i);
                }
            }
        }
        yytoken_str += "
                }
            }";
        let yytoken_fn : syn::ItemFn = syn::parse_str(&yytoken_str).unwrap();
        yytoken_fn.to_tokens(&mut src);

        /* Return the number of entries in the yy_action table */
        generate_const(&mut src, "YY_ACTTAB_COUNT", "i32", acttab.a_action.len());
        generate_array(&mut src, "YY_ACTION", &yyactiontype,
            acttab.a_action.iter().map(|ac| {
                match ac {
                    None => self.states.len() + self.rules.len() + 2,
                    Some(a) => a.action,
                }
            })
        );

        /* Output the yy_lookahead table */
        generate_array(&mut src, "YY_LOOKAHEAD", &yycodetype,
            acttab.a_action.iter().map(|ac| {
                match ac {
                    None => self.nsymbol,
                    Some(a) => a.lookahead,
                }
            })
        );

        /* Output the yy_shift_ofst[] table */
        let (n,_) = self.states.iter().enumerate().rfind(|(_,st)|
                        st.borrow().i_tkn_ofst.is_some()
                    ).unwrap();
        generate_const(&mut src, "YY_SHIFT_USE_DFLT", "i32", min_tkn_ofst - 1);
        generate_const(&mut src, "YY_SHIFT_COUNT", "i32", n);
        generate_const(&mut src, "YY_SHIFT_MIN", "i32", min_tkn_ofst);
        generate_const(&mut src, "YY_SHIFT_MAX", "i32", max_tkn_ofst);
        generate_array(&mut src, "YY_SHIFT_OFST", minimum_size_type(true, max_tkn_ofst as usize),
            self.states[0..=n].iter().map(|stp| {
                let stp = stp.borrow();
                let ofst = stp.i_tkn_ofst.unwrap_or(min_tkn_ofst - 1);
                ofst
            })
        );

        /* Output the yy_reduce_ofst[] table */
        let (n,_) = self.states.iter().enumerate().rfind(|(_,st)|
                        st.borrow().i_nt_ofst.is_some()
                    ).unwrap();
        generate_const(&mut src, "YY_REDUCE_USE_DFLT", "i32", min_nt_ofst - 1);
        generate_const(&mut src, "YY_REDUCE_COUNT", "i32", n);
        generate_const(&mut src, "YY_REDUCE_MIN", "i32", min_nt_ofst);
        generate_const(&mut src, "YY_REDUCE_MAX", "i32", max_nt_ofst);
        generate_array(&mut src, "YY_REDUCE_OFST", minimum_size_type(true, max_nt_ofst as usize),
            self.states[0..=n].iter().map(|stp| {
                let stp = stp.borrow();
                let ofst = stp.i_nt_ofst.unwrap_or(min_nt_ofst - 1);
                ofst
            })
        );

        generate_array(&mut src, "YY_DEFAULT", &yyactiontype,
            self.states.iter().map(|stp| {
                let stp = stp.borrow();
                stp.i_dflt
            })
        );

        /* Generate the table of fallback tokens. */
        let mx = self.symbols.iter().enumerate().rfind(|(_,sy)|
                        sy.borrow().fallback.is_some()
                    ).map_or(0, |(x,_)| x + 1);
        generate_array(&mut src, "YY_FALLBACK", "i32",
            self.symbols[0..mx].iter().map(|p| {
                let p = p.borrow();
                match p.fallback {
                    None => {
                        Ok(0)
                    }
                    Some(ref fb) => {
                        let fb = fb.upgrade();
                        let fb = fb.borrow();
                        match (fb.dt_num, p.dt_num) {
                            (None, _) => {}
                            (Some(fdt), Some(pdt)) if fdt == pdt => {}
                            _ => {
                                return error("Fallback token must have the same type or no type at all");
                            }
                        }
                        Ok(fb.index)
                    }
                }
            }).collect::<Result<Vec<_>,_>>()?
        );

        /* Generate the table of rule information
         **
         ** Note: This code depends on the fact that rules are number
         ** sequentually beginning with 0.
         */
        generate_array(&mut src, "YY_RULE_INFO", &yycodetype,
            self.rules.iter().map(|rp| {
                let lhs = rp.borrow().lhs.upgrade();
                let lhs = lhs.borrow();
                lhs.index
            })
        );

        let unit_type = syn::parse_str("()").unwrap();
        let yyextratype = self.arg.as_ref().unwrap_or(&unit_type);

        let mut yy_generics_with_cb = yytoken.generics.clone();
        yy_generics_with_cb.params.push(parse_quote!{ CB: PomeloCallback<#yyextratype> } );

        let (yy_generics_with_cb_impl, yy_generics_with_cb, yy_generics_with_cb_where) = yy_generics_with_cb.split_for_impl();

        src.extend(quote!{
            struct YYStackEntry #yy_generics_impl #yy_generics_where {
                stateno: i32,   /* The state-number */
                major: i32,     /* The major token value.  This is the code
                                 ** number for the token at this stack level */
                minor: YYMinorType #yy_generics,    /* The user-supplied minor token value.  This
                                        ** is the value of the token  */
            }

            pub struct Parser #yy_generics_with_cb_impl #yy_generics_with_cb_where {
                yyerrcnt: i32, /* Shifts left before out of the error */
                yystack: Vec<YYStackEntry #yy_generics>,
                extra: #yyextratype,
                cb: CB,
            }

            impl #yy_generics_with_cb_impl Parser #yy_generics_with_cb #yy_generics_with_cb_where {
                pub fn new(extra: #yyextratype, cb: CB) -> Self {
                    let mut p = Parser { yyerrcnt: -1, yystack: Vec::new(), extra: extra, cb};
                    p.yystack.push(YYStackEntry{stateno: 0, major: 0, minor: YYMinorType::YY0});
                    p
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
                pub fn parse(&mut self, token: Token #yy_generics) -> Result<(), CB::Error> {
                    let (a, b) = token_value(token);
                    yy_parse_token(self, a, b)
                }
                pub fn parse_eoi(mut self) -> Result<#yyextratype, CB::Error> {
                    yy_parse_token(&mut self, 0, YYMinorType::YY0)?;
                    Ok(self.extra)
                }
            }

            fn yy_parse_token #yy_generics_with_cb_impl(yy: &mut Parser #yy_generics_with_cb,
                                                        yymajor: i32, yyminor: YYMinorType #yy_generics) -> Result<(), CB::Error>
                #yy_generics_with_cb_where {
                let yyendofinput = yymajor==0;
                let mut yyerrorhit = false;
                if yy.yystack.is_empty() {
                    panic!("Cannot call parse after failure");
                }

                while !yy.yystack.is_empty() {
                    let yyact = yy_find_shift_action(yy, yymajor);
                    if yyact < YYNSTATE {
                        assert!(!yyendofinput);  /* Impossible to shift the $ token */
                        yy_shift(yy, yyact, yymajor, yyminor);
                        yy.yyerrcnt -= 1;
                        break;
                    } else if yyact < YYNSTATE + YYNRULE {
                        yy_reduce(yy, yyact - YYNSTATE)?;
                    } else {
                        /* A syntax error has occurred.
                         ** The response to an error depends upon whether or not the
                         ** grammar defines an error token "ERROR".
                         */
                        assert!(yyact == YYNSTATE+YYNRULE);
                        if YYERRORSYMBOL != 0 {
                            /* This is what we do if the grammar does define ERROR:
                             **
                             **  * Call the %syntax_error function.
                             **
                             **  * Begin popping the stack until we enter a state where
                             **    it is legal to shift the error symbol, then shift
                             **    the error symbol.
                             **
                             **  * Set the error count to three.
                             **
                             **  * Begin accepting and shifting new tokens.  No new error
                             **    processing will occur until three tokens have been
                             **    shifted successfully.
                             **
                             */
                            if yy.yyerrcnt < 0 {
                                yy_syntax_error(yy, yymajor, &yyminor);
                            }
                            let yymx = yy.yystack[yy.yystack.len() - 1].major;
                            if yymx==YYERRORSYMBOL || yyerrorhit {
                                break;
                            } else {
                                let mut yyact;
                                while !yy.yystack.is_empty() {
                                    yyact = yy_find_reduce_action(yy, YYERRORSYMBOL);
                                    if yyact < YYNSTATE {
                                        if !yyendofinput {
                                            yy_shift(yy, yyact, YYERRORSYMBOL, YYMinorType::YY0);
                                        }
                                        break;
                                    }
                                    yy.yystack.pop().unwrap();
                                }
                                if yy.yystack.is_empty() || yyendofinput {
                                    return Err(yy_parse_failed(yy));
                                }
                            }
                            yy.yyerrcnt = 3;
                            yyerrorhit = true;
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
                            if yy.yyerrcnt <= 0 {
                                yy_syntax_error(yy, yymajor, &yyminor);
                            }
                            yy.yyerrcnt = 3;
                            if yyendofinput {
                                return Err(yy_parse_failed(yy));
                            }
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
            fn yy_find_shift_action #yy_generics_with_cb_impl(yy: &mut Parser #yy_generics_with_cb, look_ahead: i32) -> i32 #yy_generics_with_cb_where {

                let stateno = yy.yystack[yy.yystack.len() - 1].stateno;

                if stateno > YY_SHIFT_COUNT {
                    return YY_DEFAULT[stateno as usize] as i32;
                }
                let i = YY_SHIFT_OFST[stateno as usize] as i32;
                if i == YY_SHIFT_USE_DFLT {
                    return YY_DEFAULT[stateno as usize] as i32;
                }
                assert!(look_ahead != YYNOCODE);
                let i = i + look_ahead;

                if i < 0 || i >= YY_ACTTAB_COUNT || YY_LOOKAHEAD[i as usize] as i32 != look_ahead {
                    if look_ahead > 0 {
                        if (look_ahead as usize) < YY_FALLBACK.len() {
                            let fallback = YY_FALLBACK[look_ahead as usize];
                            if fallback != 0 {
                                return yy_find_shift_action(yy, fallback);
                            }
                        }
                        if YYWILDCARD > 0 {
                            let j = i - look_ahead + (YYWILDCARD as i32);
                            if j >= 0 && j < YY_ACTTAB_COUNT && YY_LOOKAHEAD[j as usize]==YYWILDCARD {
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
            fn yy_find_reduce_action #yy_generics_with_cb_impl(yy: &mut Parser #yy_generics_with_cb, look_ahead: i32) -> i32 #yy_generics_with_cb_where {
                let stateno = yy.yystack[yy.yystack.len() - 1].stateno;
                if YYERRORSYMBOL != 0 && stateno > YY_REDUCE_COUNT {
                    return YY_DEFAULT[stateno as usize] as i32;
                }
                assert!(stateno <= YY_REDUCE_COUNT);
                let i = YY_REDUCE_OFST[stateno as usize] as i32;
                assert!(i != YY_REDUCE_USE_DFLT);
                assert!(look_ahead != YYNOCODE );
                let i = i + look_ahead;
                if YYERRORSYMBOL != 0 && (i < 0 || i >= YY_ACTTAB_COUNT || YY_LOOKAHEAD[i as usize] as i32 != look_ahead) {
                    return YY_DEFAULT[stateno as usize] as i32;
                }
                assert!(i >= 0 && i < YY_ACTTAB_COUNT);
                assert!(YY_LOOKAHEAD[i as usize] as i32 == look_ahead);
                return YY_ACTION[i as usize] as i32;
            }


            fn yy_shift #yy_generics_with_cb_impl(yy: &mut Parser #yy_generics_with_cb, new_state: i32, major: i32, minor: YYMinorType #yy_generics) #yy_generics_with_cb_where {
                yy.yystack.push(YYStackEntry{stateno: new_state, major: major, minor: minor});
            }
            fn yy_parse_failed #yy_generics_with_cb_impl(yy: &mut Parser #yy_generics_with_cb) -> CB::Error
                #yy_generics_with_cb_where {
                yy.yystack.clear();
                yy.cb.parse_fail(&mut yy.extra)
            }
            fn yy_syntax_error #yy_generics_with_cb_impl(yy: &mut Parser #yy_generics_with_cb, yymajor: i32, yyminor: &YYMinorType #yy_generics)
                #yy_generics_with_cb_where {
                //TODO send token
                yy.cb.syntax_error(&mut yy.extra);
            }
            fn yy_accept #yy_generics_with_cb_impl(yy: &mut Parser #yy_generics_with_cb) -> Result<(), CB::Error>
                #yy_generics_with_cb_where {
                yy.yystack.clear();
                yy.cb.parse_accept(&mut yy.extra)
            }
        });


        // Beginning here are the reduction cases
        let mut yyreduce_str = format!("fn yy_reduce {}(yy: &mut Parser {}, yyruleno: i32) -> Result<(), CB::Error>
            {} {{
            let yygotominor: YYMinorType {} = match yyruleno {{",
                tokens_to_string(&yy_generics_with_cb_impl),
                tokens_to_string(&yy_generics_with_cb),
                tokens_to_string(&yy_generics_with_cb_where),
                tokens_to_string(&yy_generics));

        /* Generate code which execution during each REDUCE action */
        /* First output rules other than the default: rule */
        //TODO avoid dumping the same code twice
        for rp in &self.rules {
            let mut rp = rp.borrow();
            let code = self.translate_code(&rp)?;
            yyreduce_str += &format!(" {} => {{ {} }}", rp.index, code);
        }

        /* Finally, output the default: rule.  We choose as the default: all
         ** empty actions. */
        yyreduce_str += "_ => unreachable!(),
                };
                let yygoto = YY_RULE_INFO[yyruleno as usize] as i32;
                let yyact = yy_find_reduce_action(yy, yygoto);
                if yyact < YYNSTATE {
                    yy_shift(yy, yyact, yygoto, yygotominor);
                    Ok(())
                } else {
                    assert!(yyact == YYNSTATE + YYNRULE + 1);
                    yy_accept(yy)
                }
            }";
        //println!("---------------\n{}\n----------------\n", yyreduce_str);
        let yyreduce_fn : syn::ItemFn = syn::parse_str(&yyreduce_str).unwrap();
        yyreduce_fn.to_tokens(&mut src);

        Ok(src)
    }

    /*
     ** zCode is a string that is the action associated with a rule.  Expand
     ** the symbols in this string so that the refer to elements of the parser
     ** stack.
     */
    fn translate_code(&self, rp: &Rule) -> io::Result<String> {
        let lhs = rp.lhs.upgrade();
        let lhs = lhs.borrow();
        let mut code = String::new();
        let err_sym = self.err_sym.upgrade();

        for (i, r) in rp.rhs.iter().enumerate().rev() {
            let r = r.0.upgrade();
            let r = r.borrow();
            let dt = match r.typ {
                MultiTerminal(ref ss) => {
                    let rr = ss.first().unwrap().upgrade();
                    let dt_num = rr.borrow().dt_num;
                    dt_num
                }
                _ => r.dt_num,
            };
            match dt {
                Some(_) => {
                    code += &format!("let yyp{} = yy.yystack.pop().unwrap();\n", i);
                }
                None => {
                    code += &format!("yy.yystack.pop().unwrap();\n");
                }
            }
        }
        let mut refutable = false;
        code += "let ref mut extra = yy.extra;\n";
        code += "let yyres : ";
        if let Some(ref dt) = lhs.data_type {
            code += &tokens_to_string(dt);
        } else {
            code += "()";
        }

        code += " = match (";
        for (i, r) in rp.rhs.iter().enumerate() {
            let r_ = r.0.upgrade();
            let ref alias = r.1;
            let r = r_.borrow();
            let dt = match r.typ {
                MultiTerminal(ref ss) => {
                    let rr = ss.first().unwrap().upgrade();
                    let dt_num = rr.borrow().dt_num;
                    dt_num
                }
                _ => r.dt_num,
            };
            if !Rc::ptr_eq(&r_, &err_sym) && dt.is_some() {
                refutable = true;
                code += &format!("yyp{}.minor,", i);
            }
            match (alias, &r.typ) {
                (Some(_), MultiTerminal(ref ss)) => {
                    for or in &ss[1..] {
                        let or = or.upgrade();
                        if dt != or.borrow().dt_num {
                            return error("Compound tokens must have all the same type");
                        }
                    }
                }
                _ => {}
            }
        }

        code += ") {\n    (";

        for (_i, r) in rp.rhs.iter().enumerate() {
            let r_ = r.0.upgrade();
            let ref alias = r.1;
            let r = r_.borrow();
            let dt = match r.typ {
                MultiTerminal(ref ss) => {
                    let rr = ss.first().unwrap().upgrade();
                    let dt_num = rr.borrow().dt_num;
                    dt_num
                }
                _ => r.dt_num,
            };
            if !Rc::ptr_eq(&r_, &err_sym) && dt.is_some() {
                code += &format!("YYMinorType::YY{}({}),", dt.unwrap(), alias.as_ref().map_or("_", String::as_str));
            }
        }
        code += ") => {\n";

        if let Some(ref rule_code) = rp.code {
            code += &rule_code.to_string();
        }

        if refutable {
            code += "\n    }\n    _ => unreachable!()\n};\n";
        } else {
            code += "\n    }\n};\n";
        }

        match lhs.dt_num {
            Some(ref dt) => {
                code += &format!("YYMinorType::YY{}(yyres)\n", dt);
            }
            None => {
                code += " YYMinorType::YY0\n";
            }
        }

        Ok(code)
    }
}
