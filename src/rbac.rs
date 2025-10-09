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
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Permissions {
    Read,
    Write,
    Comment,
    Delete,
    ManageUsers,
    ConfigureSystem,
}

#[reflect]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Role {
    Admin,
    User,
    Guest,
}

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

// EXERCISE: complete the implementation of method `permissions` *method*

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

    // RJ: why is this not IFF?
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

#[spec(fn(r1: Role, r2: Role) -> bool[r1 == r2])]
fn test_eq(r1: Role, r2: Role) -> bool {
    r1 == r2
}

// flux_core::eq!(Role);
#[specs {
    impl PartialEq for Role {
        #[reft] fn eq(self: Role, other: Role) -> bool {
                self == other
        }

        fn eq(&Role[@r1], other: &Role[@r2]) -> bool[<Role as PartialEq>::eq(r1, r2)];
    }
}]
const _: () = ();



// --------------------------------------------------------------------------------------------

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

impl User {
    fn new(name: String, role: Role) -> Self {
        Self {
            name,
            role,
            allow: RSet::new(),
            deny: RSet::new(),
        }
    }

    #[spec(fn(me: &mut Self[@u], p:Permissions) ensures me: Self)]
    fn allow(&mut self, p: Permissions) {
        if self.role.check_permission(&p) && !self.deny.contains(&p) {
            self.allow.insert(p);
        } else {
            panic!("Cannot allow permission {:?} for role {:?}", p, self.role);
        }
    }

    #[spec(fn(me: &mut Self[@u], p:Permissions) ensures me: Self)]
    fn deny(&mut self, p: Permissions) {
        if !self.allow.contains(&p) {
            self.deny.insert(p);
        }
    }
}