# Rust style guide

## Items

Items consist of the set of things permitted at the top level of a module.
However, Rust also allows some items to appear within some other types of
items, such as within a function. The same formatting conventions apply
whether an item appears at module level or within another item.

`extern crate` statements must be first in a file. They must be ordered
alphabetically.

`use` statements, and module declarations (`mod foo;`, not `mod { ... }`)
must come before other items. Put imports before module declarations.
Version-sort each, except that `self` and `super` must come before any other
names.

Don't automatically move module declarations annotated with `#[macro_use]`,
since that might change semantics.

## Imports (`use` statements)

From the [Rust style guide](https://doc.rust-lang.org/nightly/style-guide/items.html#imports-use-statements).

Format imports on one line where possible. Don't put spaces around braces.

```rust
use a::b::c;
use a::b::d::*;
use a::b::{foo, bar, baz};
```

### Large list imports

Prefer to use multiple imports rather than a multi-line import. However,
tools should not split imports by default.

If an import does require multiple lines (either because a list of single
names does not fit within the max width, or because of the rules for nested
imports below), then break after the opening brace and before the closing
brace, use a trailing comma, and block indent the names.

```rust
// Prefer
foo::{long, list, of, imports};
foo::{more, imports};

// If necessary
foo::{
    long, list, of, imports, more,
    imports,  // Note trailing comma
};
```

### Ordering of imports

A *group* of imports is a set of imports on the same or sequential lines.
One or more blank lines or other items (e.g., a function) separate groups of
imports.

Within a group of imports, imports must be version-sorted. Groups of imports
must not be merged or re-ordered.

E.g., input:

```rust
use d;
use c;

use b;
use a;
```

output:

```rust
use c;
use d;

use a;
use b;
```

Because of `macro_use`, attributes must also start a new group and prevent
re-ordering.

### Ordering list import

Names in a list import must be version-sorted, except that:

* `self` and `super` always come first if present, and
* groups and glob imports always come last if present.

This applies recursively. For example, `a::*` comes before `b::a` but `a::b`
comes before `a::*`. E.g.,
`use foo::bar::{a, b::c, b::d, b::d::{x, y, z}, b::{self, r, s}};`.

### Normalisation

Tools must make the following normalisations, recursively:

* `use a::self;` -> `use a;`
* `use a::{};` -> (nothing)
* `use a::{b};` -> `use a::b;`

Tools must not otherwise merge or un-merge import lists or adjust glob
imports (without an explicit option).

### Nested imports

If there are any nested imports in a list import, then use the multi-line
form, even if the import fits on one line. Each nested import must be on its
own line, but non-nested imports must be grouped on as few lines as possible.

For example,

```rust
use a::b::{
    x, y, z,
    u::{...},
    w::{...},
};
```

### Merging/un-merging imports

An example:

```rust
// Un-merged
use a::b;
use a::c::d;

// Merged
use a::{b, c::d};
```

Tools must not merge or un-merge imports by default. They may offer merging
or un-merging as an option.
