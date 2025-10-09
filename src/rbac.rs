extern crate flux_core;

use crate::rset;
use flux_rs::{assert, attrs::*};
// use flux_core::eq;

use std::rc::Rc;

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
    ManageUsers,
    ConfigureSystem,
}

#[spec(fn(r1: Permissions, r2: Permissions) -> bool[r1 == r2])]
fn test_eq_perm(r1: Permissions, r2: Permissions) -> bool {
    r1 == r2
}

#[cfg(flux)]
flux_core::eq!(Permissions);


#[reflect]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Role {
    Admin,
    User,
    Guest,
}

#[spec(fn(r1: Role, r2: Role) -> bool[r1 == r2])]
fn test_eq(r1: Role, r2: Role) -> bool {
    r1 == r2
}

#[cfg(flux)]
flux_core::eq!(Role);


defs! {

    fn admin_permissions() -> Set<Permissions> {
        set_add(Permissions::Read,
        set_add(Permissions::Write,
        set_add(Permissions::Delete,
        set_add(Permissions::ManageUsers,
        set_add(Permissions::ConfigureSystem,
        set_emp())))))
    }

    fn user_permissions() -> Set<Permissions> {
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
        } else if r == Role::User {
            user_permissions()
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
            Role::Admin => rset!(Permissions::Read, Permissions::Write, Permissions::Delete, Permissions::ManageUsers, Permissions::ConfigureSystem),
            Role::User => rset!(Permissions::Read, Permissions::Write, Permissions::Comment),
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
        let user = Role::User;   // const-promotion
        match p {
            Permissions::Read => true,
            Permissions::Write => *self == admin || *self == user,
            Permissions::Comment => *self == user,
            Permissions::Delete
            | Permissions::ManageUsers
            | Permissions::ConfigureSystem => *self == admin,
        }
    }
}






// --------------------------------------------------------------------------------------------

// Rationale for both `allow` and `deny` sets is
// you CANNOT `allow` (resp. deny) things that are `deny`ed (resp. `allow`ed)
// That is: once something is in `deny` it CANNOT be `allow`ed
#[refined_by(role: Role, allow: Set<Permissions>, deny: Set<Permissions>)]
#[invariant(set_subset(allow, permissions(role)))]
#[invariant(set_is_disjoint(allow, deny))]
#[derive(Debug)]
struct User {
    name: String,

    #[field(Role[role])]
    role: Role,

    // Invariant: allow ⊆ role.permissions()
    #[field(RSet<Permissions>[allow])]
    allow: RSet<Permissions>,

    // Invariant: allow ∩ deny = ∅
    #[field(RSet<Permissions>[deny])]
    deny: RSet<Permissions>,
}

defs! {
    fn can_allow(u: User, p: Permissions) -> bool {
        set_is_in(p, permissions(u.role)) && !set_is_in(p, u.deny)
    }

    fn can_deny(u: User, p: Permissions) -> bool {
        !set_is_in(p, u.allow)
    }

    fn upd_allow(u: User, p: Permissions) -> Set<Permissions> {
        if can_allow(u, p) {
            set_add(p, u.allow)
        } else {
            u.allow
        }
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