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

#[cfg(feature = "log")]
use baid64::DisplayBaid64;

use super::{Lib, Marshaller};
use crate::isa::{Bytecode, BytecodeRead, ExecStep, Instruction};
use crate::{Core, LibId, LibSite, Site};

impl Lib {
    /// Execute library code starting at entrypoint.
    ///
    /// # Returns
    ///
    /// Location for the external code jump, if any.
    pub fn exec<Instr>(
        &self,
        entrypoint: u16,
        core: &mut Core<LibId, Instr::Core>,
        context: &Instr::Context<'_>,
    ) -> Option<LibSite>
    where
        Instr: Instruction<LibId> + Bytecode<LibId>,
    {
        #[cfg(feature = "log")]
        let (m, w, d, g, r, y, z) = (
            "\x1B[0;35m",
            "\x1B[1;1m",
            "\x1B[0;37;2m",
            "\x1B[0;32m",
            "\x1B[0;31m",
            "\x1B[0;33m",
            "\x1B[0m",
        );

        let mut marshaller = Marshaller::with(&self.code, &self.data, &self.libs);
        let lib_id = self.lib_id();

        #[cfg(feature = "log")]
        let lib_mnemonic = lib_id.to_baid64_mnemonic();
        #[cfg(feature = "log")]
        let lib_ref = lib_mnemonic.split_at(5).0;

        if marshaller.seek(entrypoint).is_err() {
            core.reset_ck();
            #[cfg(feature = "log")]
            eprintln!("jump to non-existing offset; halting, {y}CK{z} is set to {r}false{z}");
            return None;
        }

        #[cfg(feature = "log")]
        let mut ck0 = core.ck();
        #[cfg(feature = "log")]
        let mut co0 = core.co();

        while !marshaller.is_eof() {
            let pos = marshaller.pos();

            let instr = Instr::decode_instr(&mut marshaller).ok()?;

            #[cfg(feature = "log")]
            let mut prev = bmap![];

            #[cfg(feature = "log")]
            let mut src_empty = true;
            #[cfg(feature = "log")]
            {
                for reg in instr.dst_regs() {
                    prev.insert(reg, core.get(reg));
                }
                eprint!("{m}{}@{pos:06X}.h:{z} {: <32}; ", lib_ref, instr.to_string());
                let src_regs = instr.src_regs();
                src_empty = src_regs.is_empty();
                let mut iter = src_regs.into_iter().peekable();
                while let Some(reg) = iter.next() {
                    eprint!("{d}{reg}{z} ");
                    if let Some(val) = core.get(reg) {
                        eprint!("{w}{}{z}", val);
                    } else {
                        eprint!("{d}~{z}");
                    }
                    if iter.peek().is_some() {
                        eprint!(", ");
                    }
                }
            }

            let next = instr.exec(Site::new(lib_id, pos), core, context);

            #[cfg(feature = "log")]
            {
                if !src_empty {
                    if !prev.is_empty() {
                        eprint!(" => ");
                    } else if ck0 != core.ck() || co0 != core.co() || next != ExecStep::Next {
                        eprint!("; ");
                    }
                }

                let mut iter = instr.dst_regs().into_iter().peekable();
                while let Some(reg) = iter.next() {
                    eprint!("{g}{reg}{z} ");
                    if let Some(val) = prev.get(&reg).unwrap() {
                        eprint!("{y}{}{z}", val);
                    } else {
                        eprint!("{d}~{z}");
                    }
                    eprint!(" -> ");
                    if let Some(val) = core.get(reg) {
                        eprint!("{y}{}{z}", val);
                    } else {
                        eprint!("{d}~{z}");
                    }
                    if iter.peek().is_some() {
                        eprint!(", ");
                    }
                }
                if !prev.is_empty() && (ck0 != core.ck() || co0 != core.co()) {
                    eprint!(", ");
                }
                if ck0 != core.ck() {
                    let p = if ck0.is_ok() { g } else { r };
                    let c = if core.ck().is_ok() { g } else { r };
                    eprint!("{y}CK{z} {p}{ck0}{z} -> {c}{}{z}", core.ck());
                }
                if ck0 != core.ck() && co0 != core.co() {
                    eprint!(", ");
                }
                if co0 != core.co() {
                    let p = if co0.is_ok() { g } else { r };
                    let c = if core.co().is_ok() { g } else { r };
                    eprint!("{y}CO{z} {p}{co0}{z} -> {c}{}{z}", core.co());
                }
                if (!prev.is_empty() || ck0 != core.ck() || co0 != core.co())
                    && next != ExecStep::Next
                {
                    eprint!(", ");
                }

                ck0 = core.ck();
                co0 = core.co();
            }

            if !core.acc_complexity(instr.complexity()) {
                let _ = core.fail_ck();
                #[cfg(feature = "log")]
                eprintln!("halting, complexity overflow");
                return None;
            }
            match next {
                ExecStep::Stop => {
                    #[cfg(feature = "log")]
                    {
                        let c = if core.ck().is_ok() { g } else { r };
                        eprintln!(
                            "execution stopped; {y}CK{z} {c}{}{z}, {y}CO{z} {c}{}{z}",
                            core.ck(),
                            core.co()
                        );
                    }
                    return None;
                }
                ExecStep::Fail => {
                    #[cfg(feature = "log")]
                    eprint!("{y}CK{z} {g}success{z} -> {r}fail{z}");
                    if core.fail_ck() {
                        #[cfg(feature = "log")]
                        eprintln!(", {y}CH{z} is {g}true{z}: halting");
                        return None;
                    }
                    #[cfg(feature = "log")]
                    eprintln!(", {y}CH{z} is {r}false{z}: continuing");
                    continue;
                }
                ExecStep::Next => {
                    #[cfg(feature = "log")]
                    eprintln!();
                    continue;
                }
                ExecStep::Jump(pos) => {
                    #[cfg(feature = "log")]
                    eprintln!("{d}jumping{z} {m}@{pos:06X}{z}");
                    if marshaller.seek(pos).is_err() {
                        let _ = core.fail_ck();
                        #[cfg(feature = "log")]
                        eprintln!(
                            "jump to non-existing offset: unconditionally halting; {y}CK{z} is \
                             set to {r}fail{z}"
                        );
                        return None;
                    }
                }
                ExecStep::Call(site) => {
                    #[cfg(feature = "log")]
                    eprintln!("{d}calling{z} {m}{site}{z}");
                    return Some(site.into());
                }
            }
        }

        None
    }
}
