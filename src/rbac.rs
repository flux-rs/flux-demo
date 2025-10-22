extern crate flux_core;
use crate::rset;
use flux_rs::{assert, attrs::*};

use crate::rset::*;

fn test() {
    let x = 1;
    let y = 2;
    let z = 3;
    assert(x + x == y);
}

#[reflect]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Permissions {
    Read,
    Write,
    Comment,
    Delete,
    ConfigureSystem,
}

// flux_core::eq!(Permissions);

#[specs {
    impl std::cmp::PartialEq for Permissions {
        #[reft]
        fn is_eq(p1: Permissions, p2: Permissions, v:bool) -> bool {
            v <=> (p1 == p2)
        }
        #[reft] fn is_ne(p1: Permissions, p2: Permissions, v:bool) -> bool {
            v <=> (p1 != p2)
        }
        fn eq(&Self[@r1], &Self[@r2]) -> bool[r1 == r2];
    }
}]
const _: () = ();



fn test_eq_perm(p1: Permissions, p2: Permissions) {
    let read = Permissions::Read; // const-promotion
    let write = Permissions::Write; // const-promotion
    assert(read == read);
    assert(read != write);
}


#[reflect]
#[derive(Debug, Clone, Copy, Eq )]
pub enum Role {
    Admin,
    Member,
    Guest,
}

impl PartialEq for Role {
    #[spec(fn(&Self[@r1], &Self[@r2]) -> bool[r1 == r2])]
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Role::Admin, Role::Admin) => true,
            (Role::Member, Role::Member) => true,
            (Role::Guest, Role::Guest) => true,
            _ => false,
        }
    }

    #[spec(fn(&Self[@r1], &Self[@r2]) -> bool[r1 != r2])]
    fn ne(&self, other: &Self) -> bool {
        !self.eq(other)
    }
}

fn test_role_eq() {
  let admin = Role::Admin;
  let member = Role::Member;
  assert(admin == admin);
  assert(admin != member);
  assert(member == member);
}

#[spec(fn(&Role[@r]) -> bool[r == Role::Admin])]
fn is_admin_eq(r: &Role) -> bool {
    let admin = Role::Admin; // const-promotion
    *r == admin
}

#[spec(fn(&Role[@r]) -> bool[r == Role::Admin])]
pub fn is_admin(r: &Role) -> bool {
    match r {
        Role::Admin => true,
        _ => false,
    }
}

#[spec(fn(r1: Role, r2: Role) -> bool[r1 == r2])]
fn test_eq(r1: Role, r2: Role) -> bool {
    r1 == r2
}


defs! {

    fn admin_permissions() -> Set<Permissions> {
        set_add(Permissions::Read,
        set_add(Permissions::Write,
        set_add(Permissions::Delete,
        set_add(Permissions::ConfigureSystem,
        set_emp()))))
    }

    fn member_permissions() -> Set<Permissions> {
        set_add(Permissions::Read,
        set_add(Permissions::Write,
        set_add(Permissions::Comment,
        set_emp())))
    }

    fn guest_permissions() -> Set<Permissions> {
        set_add(Permissions::Read,
        set_emp())
    }


    fn permissions(r:Role) -> Set<Permissions> {
        if r == Role::Admin {
            admin_permissions()
        } else if r == Role::Member {
            member_permissions()
        } else {
            guest_permissions()
        }
    }
}

// EXERCISE: complete the implementation of method `permissions`

impl Role {

    #[spec(fn(&Self[@r]) -> RSet<Permissions>[permissions(r)])]
    pub fn permissions(&self) -> RSet<Permissions> {
        match self {
            Role::Admin => rset!(Permissions::Read, Permissions::Write, Permissions::Delete, Permissions::ConfigureSystem),
            Role::Member => rset!(Permissions::Read, Permissions::Write, Permissions::Comment),
            Role::Guest => rset!(Permissions::Read),
        }
    }

    #[spec(fn(&Self[@r], &Permissions[@p]) -> bool[set_is_in(p, permissions(r))])]
    pub fn check_permission(&self, p: &Permissions) -> bool {
        self.permissions().contains(p)
    }

    // EXERCISE: Fix the bug? (lump write/comment) together?
    #[spec(fn(&Self[@r], &Permissions[@p]) -> bool[set_is_in(p, permissions(r))])]
    pub fn check_permission_match(&self, p: &Permissions) -> bool {
        let admin = Role::Admin; // const-promotion
        let user = Role::Member;   // const-promotion
        match p {
            Permissions::Read => true,
            Permissions::Write => *self == admin || *self == user,
            Permissions::Comment => *self == user,
            Permissions::Delete
            | Permissions::ConfigureSystem => *self == admin,
        }
    }
}




fn test_set_add() {
  let read = Permissions::Read;
  let write = Permissions::Write;
  let mut s = RSet::new();
  s.insert(read);
  assert(s.contains(&read));
  assert(!s.contains(&write));
  s.insert(write);
  assert(s.contains(&read));
  assert(s.contains(&write));
}

fn test_rset_macro() {
  let read = Permissions::Read;
  let write = Permissions::Write;
  let s = rset!{read, write};
  assert(s.contains(&read) && s.contains(&write));
}

fn test_union_intersection() {
  let rd = Permissions::Read;
  let wr = Permissions::Write;
  let cm = Permissions::Comment;
  // make two sets
  let s1 = rset![rd, wr];
  let s2 = rset![wr, cm];
  // check union
  let su = s1.union(&s2);
  assert(su.contains(&rd) && su.contains(&wr) && su.contains(&cm));
  // check intersection
  let si = s1.intersection(&s2);
  assert(!si.contains(&rd) && si.contains(&wr) && !si.contains(&cm));
}

#[spec(fn(&RSet<T>[@s1], &RSet<T>[@s2]) -> bool[s1 == s2])]
fn set_eq<T:Eq+std::hash::Hash>(s1: &RSet<T>, s2: &RSet<T>) -> bool {
    s1.subset(&s2) && s2.subset(&s1)
}

// --------------------------------------------------------------------------------------------

// // Rationale for both `allow` and `deny` sets is
// // you CANNOT `allow` (resp. deny) things that are `deny`ed (resp. `allow`ed)
// // That is: once something is in `deny` it CANNOT be `allow`ed
// #[refined_by(role: Role, allow: Set<Permissions>, deny: Set<Permissions>)]
// #[invariant(set_subset(allow, permissions(role)))]
// #[invariant(set_is_disjoint(allow, deny))]
// #[derive(Debug)]
// struct User {
//     name: String,

//     #[field(Role[role])]
//     role: Role,

//     // Invariant: allow ⊆ role.permissions()
//     #[field(RSet<Permissions>[allow])]
//     allow: RSet<Permissions>,

//     // Invariant: allow ∩ deny = ∅
//     #[field(RSet<Permissions>[deny])]
//     deny: RSet<Permissions>,
// }

#[derive(Debug)]
struct User {
  name: String,
  role: Role,
  allow: RSet<Permissions>,
  deny: RSet<Permissions>,
}

#[specs {
  #[refined_by(role:Role, allow:Set<Permissions>, deny:Set<Permissions>)]
  #[invariant(set_subset(allow, permissions(role)))]
  #[invariant(set_intersection(allow, deny) == set_emp())]
  struct User {
    name: String,
    role: Role[role],
    allowed: RSet<Permissions>[allow],
    denied: RSet<Permissions>[deny],
  }
}]
const _: () = ();

use Role::*;
use Permissions::*;

fn test_user() {
    let alice = User {
        name: "Alice".to_string(),
        role: Guest,
        allow: rset!{ Read /* , Write */ },
        deny: rset!{ },
    };
    let bob = User {
        name: "Bob".to_string(),
        role: Admin,
        allow: rset!{ Read, Write, Delete },
        deny: rset!{ Write },
    };
}

defs! {
    fn can_allow(u: User, p: Permissions) -> bool {
        set_is_in(p, permissions(u.role)) && !set_is_in(p, u.deny)
    }

    fn upd_allow(u: User, p: Permissions) -> Set<Permissions> {
        if can_allow(u, p) {
            set_add(p, u.allow)
        } else {
            u.allow
        }
    }

    fn can_deny(u: User, p: Permissions) -> bool {
        !set_is_in(p, u.allow)
    }
    fn upd_deny(u: User, p: Permissions) -> Set<Permissions> {
        if can_deny(u, p) {
            set_add(p, u.deny)
        } else {
            u.deny
        }
    }
}

impl User {
    #[spec(fn(name: String, role: Role) -> Self[User { role: role, allow: set_emp(), deny: set_emp() }])]
    fn new(name: String, role: Role) -> Self {
        Self {
            name,
            role,
            allow: RSet::new(),
            deny: RSet::new(),
        }
    }

    #[spec(fn(&Self[@u], &Permissions[@p]) -> bool[set_is_in(p, u.allow)])]
    fn is_allowed(&self, p: &Permissions) -> bool {
        self.allow.contains(p)
    }

    // EXERCISE: write this spec, but give a simpler warm-up version first.

    #[spec(fn(me: &mut Self[@u], &Permissions[@p]) -> bool[can_allow(u, p)]
              ensures me: Self[User { allow: upd_allow(u, p), ..u }])]
    fn allow(&mut self, p: &Permissions) -> bool {
        if self.role.check_permission(&p) && !self.deny.contains(&p) {
            self.allow.insert(*p);
            true
        } else {
            false
        }
    }

    #[spec(fn(me: &mut Self[@u], &Permissions[@p]) -> bool[can_deny(u, p)]
              ensures me: Self[User { deny: upd_deny(u, p), ..u }])]
    fn deny(&mut self, p: &Permissions) -> bool {
        if !self.allow.contains(p) {
            self.deny.insert(*p);
            true
        } else {
            false
        }
    }
}

fn test_rbac() {
    let mut rj = User::new("rjhala".to_string(), Role::Admin);
    let mut guest = User::new("guest".to_string(), Role::Guest);

    let read = Permissions::Read;   // const-promotion
    let write = Permissions::Write; // const-promotion

    assert(rj.is_allowed(&read) == false);
    assert(rj.allow(&read));
    assert(rj.is_allowed(&read) == true);
    assert(rj.allow(&read) == true); // idempotent
    assert(rj.deny(&read) == false); // cannot deny what is allowed
    assert(rj.is_allowed(&read) == true);

    assert(guest.is_allowed(&write) == false);
    assert(guest.allow(&write) == false); // cannot allow what role does not permit
    assert(guest.is_allowed(&write) == false);
    assert(guest.deny(&write) == true);
    assert(guest.deny(&write) == true); // idempotent
    assert(guest.is_allowed(&write) == false);
}