// Copyright (C) Microsoft Corporation. All rights reserved.

//! Definitions for elf core dump handling.

use zerocopy::AsBytes;
use zerocopy::FromBytes;
use zerocopy::FromZeroes;

/// ELF header
#[derive(AsBytes, FromBytes, FromZeroes, Debug)]
#[repr(C)]
pub struct Elf64_Ehdr {
    pub e_ident: [u8; 16],
    pub e_type: u16,
    pub e_machine: u16,
    pub e_version: u32,
    pub e_entry: u64,
    pub e_phoff: u64,
    pub e_shoff: u64,
    pub e_flags: u32,
    pub e_ehsize: u16,
    pub e_phentsize: u16,
    pub e_phnum: u16,
    pub e_shentsize: u16,
    pub e_shnum: u16,
    pub e_shstrndx: u16,
}

/// Program header
#[derive(AsBytes, FromBytes, FromZeroes, Copy, Clone, Debug)]
#[repr(C)]
pub struct Elf64_Phdr {
    pub p_type: u32,
    pub p_flags: u32,
    pub p_offset: u64,
    pub p_vaddr: u64,
    pub p_paddr: u64,
    pub p_filesz: u64,
    pub p_memsz: u64,
    pub p_align: u64,
}

/// ELF note header
#[derive(AsBytes)]
#[repr(C)]
pub struct Elf64_Nhdr {
    pub namesz: u32,
    pub descsz: u32,
    pub ntype: u32,
}

/// Auxiliary information
pub const PT_NOTE: u32 = 4;