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

use alloc::collections::BTreeSet;

use super::CtrlInstr;
use crate::core::{Core, NoExt, NoRegs, Site, SiteId, Status};
use crate::isa::{ExecStep, Instr, Instruction, ReservedInstr};

impl<Id: SiteId> Instruction<Id> for Instr<Id> {
    const ISA_EXT: &'static [&'static str] = &[];

    type Core = NoExt;
    type Context<'ctx> = ();

    fn is_goto_target(&self) -> bool {
        match self {
            Instr::Ctrl(instr) => instr.is_goto_target(),
            Instr::Reserved(instr) => Instruction::<Id>::is_goto_target(instr),
        }
    }

    fn local_goto_pos(&mut self) -> Option<&mut u16> {
        match self {
            Instr::Ctrl(instr) => instr.local_goto_pos(),
            Instr::Reserved(instr) => Instruction::<Id>::local_goto_pos(instr),
        }
    }

    fn remote_goto_pos(&mut self) -> Option<&mut Site<Id>> {
        match self {
            Instr::Ctrl(instr) => instr.remote_goto_pos(),
            Instr::Reserved(instr) => Instruction::<Id>::remote_goto_pos(instr),
        }
    }

    fn src_regs(&self) -> BTreeSet<NoRegs> {
        match self {
            Instr::Ctrl(instr) => instr.src_regs(),
            Instr::Reserved(instr) => Instruction::<Id>::src_regs(instr),
        }
    }

    fn dst_regs(&self) -> BTreeSet<NoRegs> {
        match self {
            Instr::Ctrl(instr) => instr.dst_regs(),
            Instr::Reserved(instr) => Instruction::<Id>::dst_regs(instr),
        }
    }

    fn op_data_bytes(&self) -> u16 {
        match self {
            Instr::Ctrl(instr) => instr.op_data_bytes(),
            Instr::Reserved(instr) => Instruction::<Id>::op_data_bytes(instr),
        }
    }

    fn ext_data_bytes(&self) -> u16 {
        match self {
            Instr::Ctrl(instr) => instr.ext_data_bytes(),
            Instr::Reserved(instr) => Instruction::<Id>::ext_data_bytes(instr),
        }
    }

    fn exec(
        &self,
        site: Site<Id>,
        core: &mut Core<Id, Self::Core>,
        _: &Self::Context<'_>,
    ) -> ExecStep<Site<Id>> {
        match self {
            Instr::Ctrl(instr) => instr.exec(site, core, &()),
            Instr::Reserved(instr) => instr.exec(site, core, &()),
        }
    }
}

impl<Id: SiteId> Instruction<Id> for ReservedInstr {
    const ISA_EXT: &'static [&'static str] = &[];

    type Core = NoExt;
    type Context<'ctx> = ();

    fn is_goto_target(&self) -> bool { false }

    fn local_goto_pos(&mut self) -> Option<&mut u16> { None }

    fn remote_goto_pos(&mut self) -> Option<&mut Site<Id>> { None }

    fn src_regs(&self) -> BTreeSet<NoRegs> { none!() }

    fn dst_regs(&self) -> BTreeSet<NoRegs> { none!() }

    fn op_data_bytes(&self) -> u16 { none!() }

    fn ext_data_bytes(&self) -> u16 { none!() }

    fn complexity(&self) -> u64 { u64::MAX }

    fn exec(
        &self,
        _: Site<Id>,
        _: &mut Core<Id, Self::Core>,
        _: &Self::Context<'_>,
    ) -> ExecStep<Site<Id>> {
        ExecStep::Fail
    }
}

impl<Id: SiteId> Instruction<Id> for CtrlInstr<Id> {
    const ISA_EXT: &'static [&'static str] = &[];

    type Core = NoExt;
    type Context<'ctx> = ();

    fn is_goto_target(&self) -> bool {
        match self {
            CtrlInstr::Nop => true,
            CtrlInstr::ChkCo
            | CtrlInstr::ChkCk
            | CtrlInstr::NotCo
            | CtrlInstr::FailCk
            | CtrlInstr::RsetCk => false,
            CtrlInstr::Jmp { .. } | CtrlInstr::JiOvfl { .. } | CtrlInstr::JiFail { .. } => false,
            CtrlInstr::Sh { .. } | CtrlInstr::ShOvfl { .. } | CtrlInstr::ShFail { .. } => false,
            CtrlInstr::Exec { .. } | CtrlInstr::Fn { .. } | CtrlInstr::Call { .. } => false,
            CtrlInstr::Ret | CtrlInstr::Stop => false,
        }
    }

    fn local_goto_pos(&mut self) -> Option<&mut u16> {
        match self {
            CtrlInstr::Nop
            | CtrlInstr::ChkCo
            | CtrlInstr::ChkCk
            | CtrlInstr::NotCo
            | CtrlInstr::FailCk
            | CtrlInstr::RsetCk => None,
            CtrlInstr::Jmp { pos }
            | CtrlInstr::JiOvfl { pos }
            | CtrlInstr::JiFail { pos }
            | CtrlInstr::Fn { pos } => Some(pos),
            CtrlInstr::Sh { shift: _ }
            | CtrlInstr::ShOvfl { shift: _ }
            | CtrlInstr::ShFail { shift: _ } => None,
            CtrlInstr::Exec { site: _ } | CtrlInstr::Call { site: _ } => None,
            CtrlInstr::Ret | CtrlInstr::Stop => None,
        }
    }

    fn remote_goto_pos(&mut self) -> Option<&mut Site<Id>> {
        match self {
            CtrlInstr::Nop
            | CtrlInstr::ChkCo
            | CtrlInstr::ChkCk
            | CtrlInstr::NotCo
            | CtrlInstr::FailCk
            | CtrlInstr::RsetCk => None,
            CtrlInstr::Jmp { pos: _ }
            | CtrlInstr::JiOvfl { pos: _ }
            | CtrlInstr::JiFail { pos: _ }
            | CtrlInstr::Fn { pos: _ } => None,
            CtrlInstr::Sh { shift: _ }
            | CtrlInstr::ShOvfl { shift: _ }
            | CtrlInstr::ShFail { shift: _ } => None,
            CtrlInstr::Exec { site } | CtrlInstr::Call { site } => Some(site),
            CtrlInstr::Ret | CtrlInstr::Stop => None,
        }
    }

    fn src_regs(&self) -> BTreeSet<NoRegs> { none!() }

    fn dst_regs(&self) -> BTreeSet<NoRegs> { none!() }

    fn op_data_bytes(&self) -> u16 {
        match self {
            CtrlInstr::Nop
            | CtrlInstr::ChkCo
            | CtrlInstr::ChkCk
            | CtrlInstr::NotCo
            | CtrlInstr::FailCk
            | CtrlInstr::RsetCk => 0,
            CtrlInstr::Jmp { .. } | CtrlInstr::JiOvfl { .. } | CtrlInstr::JiFail { .. } => 2,
            CtrlInstr::Sh { .. } | CtrlInstr::ShOvfl { .. } | CtrlInstr::ShFail { .. } => 1,
            CtrlInstr::Exec { .. } => 2,
            CtrlInstr::Fn { .. } => 2,
            CtrlInstr::Call { .. } => 2,
            CtrlInstr::Ret | CtrlInstr::Stop => 0,
        }
    }

    fn ext_data_bytes(&self) -> u16 {
        match self {
            CtrlInstr::Nop
            | CtrlInstr::ChkCo
            | CtrlInstr::ChkCk
            | CtrlInstr::NotCo
            | CtrlInstr::FailCk
            | CtrlInstr::RsetCk => 0,
            CtrlInstr::Jmp { .. } | CtrlInstr::JiOvfl { .. } | CtrlInstr::JiFail { .. } => 0,
            CtrlInstr::Sh { .. } | CtrlInstr::ShOvfl { .. } | CtrlInstr::ShFail { .. } => 0,
            CtrlInstr::Exec { .. } => 32,
            CtrlInstr::Fn { .. } => 0,
            CtrlInstr::Call { .. } => 32,
            CtrlInstr::Ret | CtrlInstr::Stop => 0,
        }
    }

    fn exec(
        &self,
        cursor: Site<Id>,
        core: &mut Core<Id, Self::Core>,
        _: &Self::Context<'_>,
    ) -> ExecStep<Site<Id>> {
        let shift_jump = |shift: i8| {
            let Some(pos) = cursor.offset.checked_add_signed(shift as i16) else {
                return ExecStep::Fail;
            };
            ExecStep::Jump(pos)
        };

        match *self {
            CtrlInstr::Nop => {}
            CtrlInstr::ChkCo => {
                if !core.co().is_ok() {
                    return ExecStep::Fail;
                }
            }
            CtrlInstr::ChkCk => {
                if !core.ck().is_ok() {
                    return ExecStep::Stop;
                }
            }
            CtrlInstr::FailCk => {
                if core.fail_ck() {
                    return ExecStep::Stop;
                }
            }
            CtrlInstr::RsetCk => {
                core.set_co(core.ck());
                core.reset_ck()
            }
            CtrlInstr::NotCo => core.set_co(!core.co()),
            CtrlInstr::Jmp { pos } => return ExecStep::Jump(pos),
            CtrlInstr::JiOvfl { pos } => {
                if core.co() == Status::Fail {
                    return ExecStep::Jump(pos);
                }
            }
            CtrlInstr::JiFail { pos } => {
                if core.ck() == Status::Fail {
                    return ExecStep::Jump(pos);
                }
            }
            CtrlInstr::Sh { shift } => {
                return shift_jump(shift);
            }
            CtrlInstr::ShOvfl { shift } => {
                if core.co() == Status::Fail {
                    return shift_jump(shift);
                }
            }
            CtrlInstr::ShFail { shift } => {
                if core.ck() == Status::Fail {
                    return shift_jump(shift);
                }
            }
            CtrlInstr::Exec { site } => return ExecStep::Call(site),
            CtrlInstr::Fn { pos } => {
                return match core.push_cs(cursor) {
                    Some(_) => ExecStep::Jump(pos),
                    None => ExecStep::Fail,
                }
            }
            CtrlInstr::Call { site } => {
                return match core.push_cs(cursor) {
                    Some(_) => ExecStep::Call(site),
                    None => ExecStep::Fail,
                }
            }
            CtrlInstr::Ret => {
                return match core.pop_cs() {
                    Some(site) => ExecStep::Ret(site),
                    None => ExecStep::Stop,
                }
            }
            CtrlInstr::Stop => return ExecStep::Stop,
        }
        ExecStep::Next
    }
}

#[cfg(test)]
mod test {
    #![cfg_attr(coverage_nightly, coverage(off))]

    use super::*;
    use crate::{aluasm, CompiledLib, CoreConfig, LibId, LibSite, Vm};

    fn code() -> Vec<Instr<LibId>> {
        const MAIN: u16 = 0;
        const SUB: u16 = 1;
        const END: u16 = 2;

        aluasm! {
           .routine :MAIN;
            chk     CO;
            chk     CK;

            jif     CO, :MAIN;
            jif     CO, -1;

            jif     CK, :MAIN;
            jif     CK, -1;

            fail    CK;
            mov     CO, CK;
            chk     CK;
            not     CO;
            chk     CO;

            jmp     +5;
            jmp     :MAIN; // this is skipped

            call    :SUB;
            stop;

           .routine :SUB;
            jmp     :END;
           .label   :END;
            ret;
        }
    }

    #[test]
    fn run() {
        let code = code();

        let lib = CompiledLib::compile(code.clone(), &[]).unwrap().into_lib();
        let mut disasm = lib.disassemble::<Instr<_>>().unwrap();
        assert_eq!(disasm[14], CtrlInstr::Fn { pos: 27 }.into());
        assert_eq!(disasm[17], CtrlInstr::Jmp { pos: 31 }.into());
        disasm[14] = CtrlInstr::Fn { pos: 1 }.into();
        disasm[17] = CtrlInstr::Jmp { pos: 2 }.into();
        assert_eq!(disasm, code);

        let mut vm_main =
            Vm::<Instr<LibId>>::with(CoreConfig { halt: false, complexity_lim: None }, ());
        let resolver = |_: LibId| Some(&lib);
        let status = vm_main.exec(LibSite::new(lib.lib_id(), 0), &(), resolver);
        assert_eq!(status, Status::Ok);
    }

    #[test]
    fn print_disassemble() {
        let lib = CompiledLib::compile(code(), &[]).unwrap().into_lib();
        let mut buf = Vec::new();
        lib.print_disassemble::<Instr<_>>(&mut buf).unwrap();
        assert_eq!(
            String::from_utf8(buf).unwrap(),
            "@000000: nop
@000001: chk     CO
@000002: chk     CK
@000003: jif     CO, 0000
@000006: jif     CO, -1
@000008: jif     CK, 0000
@000011: jif     CK, -1
@000013: fail    CK
@000014: mov     CO, CK
@000015: chk     CK
@000016: not     CO
@000017: chk     CO
@000018: jmp     +5
@000020: jmp     0000
@000023: call    0027
@000026: stop
@000027: nop
@000028: jmp     0031
@000031: nop
@000032: ret
"
        );
    }
}
