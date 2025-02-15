// Reference rust implementation of AluVM (arithmetic logic unit virtual machine).
// To find more on AluVM please check <https://aluvm.org>
//
// SPDX-License-Identifier: Apache-2.0
//
// Designed in 2021-2025 by Dr Maxim Orlovsky <orlovsky@ubideco.org>
// Written in 2021-2025 by Dr Maxim Orlovsky <orlovsky@ubideco.org>
//
// Copyright (C) 2021-2024 LNP/BP Standards Association, Switzerland.
// Copyright (C) 2024-2025 Laboratories for Ubiquitous Deterministic Computing (UBIDECO),
//                         Institute for Distributed and Cognitive Systems (InDCS), Switzerland.
// Copyright (C) 2021-2025 Dr Maxim Orlovsky.
// All rights under the above copyrights are reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
// in compliance with the License. You may obtain a copy of the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
// or implied. See the License for the specific language governing permissions and limitations under
// the License.

/// Macro compiler for AluVM assembler.
///
/// # Example
///
/// ```
/// extern crate alloc;
///
/// use aluvm::isa::Instr;
/// use aluvm::regs::Status;
/// use aluvm::{aluasm, Lib, LibId, LibSite, Vm};
///
/// let code = aluasm! {
///     nop                 ;
///     not     CO          ;
///     put     CK, :fail   ;
///     put     CK, :ok     ;
///     chk                 ;
///     jif     CO, +2      ;
///     jif     CO, +2#h    ;
///     jif     CK, -2      ;
///     jif     CK, -2#h    ;
///     jmp     +2          ;
///     jmp     +2#h        ;
///     stop                ;
/// };
///
/// let lib = Lib::assemble::<Instr<LibId>>(&code).unwrap();
/// let mut vm = Vm::<Instr<LibId>>::new();
/// match vm.exec(LibSite::new(lib.lib_id(), 0), &(), |_| Some(&lib)) {
///     Status::Ok => println!("success"),
///     Status::Fail => println!("failure"),
/// }
/// ```
#[macro_export]
macro_rules! aluasm {
    ($( $tt:tt )+) => {{
        use $crate::instr;

        let mut code: alloc::vec::Vec<$crate::isa::Instr<$crate::LibId>> = Default::default();
        #[allow(unreachable_code)] {
            $crate::aluasm_inner! { code => $( $tt )+ }
        }
        code
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! aluasm_inner {
    // end of program
    { $code:ident => } => { };
    // no operands
    { $code:ident => $op:ident ; $($tt:tt)* } => {
        $code.push(instr!{ $op });
        $crate::aluasm_inner! { $code => $( $tt )* }
    };
    // special type
    { $code:ident => $op:ident $reg:ident, :$val:ident ; $($tt:tt)* } => {
        $code.push(instr!{ $op $reg, :$val });
        $crate::aluasm_inner! { $code => $( $tt )* }
    };
    // operand is an external jump to a named location in library literal
    { $code:ident => $op:ident $arg:literal @ $lib:ident ; $($tt:tt)* } => {
        $code.push(instr!{ $op $arg @ $lib });
        $crate::aluasm_inner! { $code => $( $tt )* }
    };
    // operand is an external jump to a hex location in library literal
    { $code:ident => $op:ident $arg:literal @ $lib:literal #h ; $($tt:tt)* } => {
        $code.push(instr!{ $op $arg @ $lib #h });
        $crate::aluasm_inner! { $code => $( $tt )* }
    };
    // operand is a positive shift
    { $code:ident => $op:ident + $pos:literal ; $($tt:tt)* } => {
        $code.push(instr!{ $op + $pos });
        $crate::aluasm_inner! { $code => $( $tt )* }
    };
    { $code:ident => $op:ident $arg:ident, + $pos:literal ; $($tt:tt)* } => {
        $code.push(instr!{ $op $arg, + $pos });
        $crate::aluasm_inner! { $code => $( $tt )* }
    };
    // operand is a negative shift
    { $code:ident => $op:ident - $pos:literal ; $($tt:tt)* } => {
        $code.push(instr!{ $op - $pos });
        $crate::aluasm_inner! { $code => $( $tt )* }
    };
    { $code:ident => $op:ident $arg:ident, - $pos:literal ; $($tt:tt)* } => {
        $code.push(instr!{ $op $arg, - $pos });
        $crate::aluasm_inner! { $code => $( $tt )* }
    };
    // operand is a positive hex shift
    { $code:ident => $op:ident + $pos:literal #h; $($tt:tt)* } => {
        $code.push(instr!{ $op + $pos #h });
        $crate::aluasm_inner! { $code => $( $tt )* }
    };
    { $code:ident => $op:ident $arg:ident, + $pos:literal #h; $($tt:tt)* } => {
        $code.push(instr!{ $op $arg, + $pos #h });
        $crate::aluasm_inner! { $code => $( $tt )* }
    };
    // operand is a negative hex  shift
    { $code:ident => $op:ident - $pos:literal #h; $($tt:tt)* } => {
        $code.push(instr!{ $op - $pos #h });
        $crate::aluasm_inner! { $code => $( $tt )* }
    };
    { $code:ident => $op:ident $arg:ident, - $pos:literal #h; $($tt:tt)* } => {
        $code.push(instr!{ $op $arg, - $pos #h });
        $crate::aluasm_inner! { $code => $( $tt )* }
    };
    // operand is an external jump to a named location in named library
    { $code:ident => $op:ident $arg:ident @ $lib:ident ; $($tt:tt)* } => {
        $code.push(instr!{ $op $arg @ $lib });
        $crate::aluasm_inner! { $code => $( $tt )* }
    };
    // operands are all literals
    { $code:ident => $op:ident $( $arg:literal ),+ ; $($tt:tt)* } => {
        $code.push(instr!{ $op $( $arg ),+ });
        $crate::aluasm_inner! { $code => $( $tt )* }
    };
    // operands are all idents
    { $code:ident => $op:ident $( $arg:ident ),+ ; $($tt:tt)* } => {
        $code.push(instr!{ $op $( $arg ),+ });
        $crate::aluasm_inner! { $code => $( $tt )* }
    };
    // operands are indents followed by literals
    { $code:ident => $op:ident $( $arg:ident ),+ $( $val:literal ),+ ; $($tt:tt)* } => {
        $code.push(instr!{ $op $( $arg ),+ $( $val ),+ });
        $crate::aluasm_inner! { $code => $( $tt )* }
    };
}

#[macro_export]
macro_rules! from_hex {
    ($ty:ty, $val:literal) => {
        <$ty>::from_str_radix(&stringify!($val), 16)
            .unwrap_or_else(|_| panic!("invalid hex literal {}", $val))
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! instr {
    (nop) => {
        $crate::isa::CtrlInstr::Nop.into()
    };
    (chk) => {
        $crate::isa::CtrlInstr::Chk.into()
    };
    (not CO) => {
        $crate::isa::CtrlInstr::NotCo.into()
    };
    (put CK, : fail) => {
        $crate::isa::CtrlInstr::FailCk.into()
    };
    (put CK, : ok) => {
        $crate::isa::CtrlInstr::RsetCk.into()
    };
    (ret) => {
        $crate::isa::CtrlInstr::Ret.into()
    };
    (stop) => {
        $crate::isa::CtrlInstr::Stop.into()
    };

    // Jumps
    (jmp $pos:literal) => {
        $crate::isa::CtrlInstr::Jmp { pos: $pos }.into()
    };
    (jmp $pos:literal #h) => {
        $crate::isa::CtrlInstr::Jmp { pos: $crate::from_hex!(u16, $pos) }.into()
    };

    (jif CO, + $shift:literal) => {
        $crate::isa::CtrlInstr::ShNe { shift: $shift }.into()
    };
    (jif CO, + $shift:literal #h) => {
        $crate::isa::CtrlInstr::ShNe { shift: $crate::from_hex!(i8, $shift) }.into()
    };
    (jif CK, - $shift:literal) => {
        $crate::isa::CtrlInstr::ShFail { shift: $shift }.into()
    };
    (jif CK, - $shift:literal #h) => {
        $crate::isa::CtrlInstr::ShFail { shift: $crate::from_hex!(i8, $shift) }.into()
    };
    (jif CO, $pos:literal) => {
        $crate::isa::CtrlInstr::JiNe { pos: $pos }.into()
    };
    (jif CO, $pos:literal #h) => {
        $crate::isa::CtrlInstr::JiNe { pos: $crate::from_hex!(u16, $pos) }.into()
    };
    (jif CK, $pos:literal) => {
        $crate::isa::CtrlInstr::JiFail { pos: $pos }.into()
    };
    (jif CK, $pos:literal #h) => {
        $crate::isa::CtrlInstr::JiFail { pos: $crate::from_hex!(u16, $pos) }.into()
    };
    (jmp + $shift:literal) => {
        $crate::isa::CtrlInstr::Sh { shift: $shift }.into()
    };
    (jmp + $shift:literal #h) => {
        $crate::isa::CtrlInstr::Sh { shift: $crate::from_hex!(i8, $shift) }.into()
    };
    (jmp - $shift:literal) => {
        $crate::isa::CtrlInstr::Sh { shift: $shift }.into()
    };
    (jmp - $shift:literal #h) => {
        $crate::isa::CtrlInstr::Sh { shift: $crate::from_hex!(i8, $shift) }.into()
    };

    // Calls
    (jmp $lib:ident @ $pos:literal) => {
        $crate::isa::CtrlInstr::Exec { site: $crate::Site::new($lib, $pos) }.into()
    };
    (jmp $lib:ident @ $pos:literal #h) => {
        $crate::isa::CtrlInstr::Exec { site: $crate::Site::new($lib, $crate::from_hex!(u16, $pos)) }
            .into()
    };
    (call $lib:ident @ $pos:literal) => {
        $crate::isa::CtrlInstr::Call { site: $crate::Site::new($lib, $pos) }.into()
    };
    (call $lib:ident @ $pos:literal #h) => {
        $crate::isa::CtrlInstr::Call { site: $crate::Site::new($lib, $crate::from_hex!(u16, $pos)) }
            .into()
    };
    (call $pos:literal) => {
        $crate::isa::CtrlInstr::Fn { pos: $pos }.into()
    };
    (call $pos:literal #h) => {
        $crate::isa::CtrlInstr::Fn { pos: from_hex!(u16, $pos) }.into()
    };
}
