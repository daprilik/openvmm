// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Download pre-built mu_msvm package from its GitHub Release.

use flowey::node::prelude::*;
use node_params::*;
use serde::de::DeserializeOwned;
use std::collections::BTreeMap;
use std::marker::PhantomData;

#[derive(Serialize, Deserialize, Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum MuMsvmArch {
    X86_64,
    Aarch64,
}

flowey_request! {
    pub enum Request {
        /// Specify version of mu_msvm to use
        Version(String),
        /// Download the mu_msvm package for the given arch
        GetMsvmFd {
            arch: MuMsvmArch,
            msvm_fd: WriteVar<PathBuf>
        }
    }
}

trait NodeParam {
    type Item<'new>;

    fn imports(ctx: &mut ImportCtx<'_>) {
        let _ = ctx;
    }

    fn retrieve(ctx: NodeCtx<'_>) -> Self::Item<'_>;
}

struct FunctionNode<Input, F> {
    f: F,
    // we need a marker because otherwise we're not using `Input`.
    // fn() -> Input is chosen because just using Input would not be `Send` + `Sync`,
    // but the fnptr is always `Send` + `Sync`.
    //
    // Also, this way Input is covariant, but that's not super relevant since we can only deal with
    // static parameters here anyway so there's no subtyping. More info here:
    // https://doc.rust-lang.org/nomicon/subtyping.html
    marker: PhantomData<fn() -> Input>,
}

trait IntoFlowNode<Input> {
    type FlowNode: FlowNodeBase;

    fn into_flow_node(self) -> Self::FlowNode;
}

impl<
        F: FnMut(HandleAll<Req>, T1, T2, T3) -> anyhow::Result<()>,
        Req: Serialize + DeserializeOwned,
        T1: NodeParam,
        T2: NodeParam,
        T3: NodeParam,
    > IntoFlowNode<(Req, T1, T2, T3)> for F
where
    for<'a, 'b> &'a mut F: FnMut(HandleAll<Req>, T1, T2, T3) -> anyhow::Result<()>
        + FnMut(
            HandleAll<Req>,
            <T1 as NodeParam>::Item<'b>,
            <T2 as NodeParam>::Item<'b>,
            <T3 as NodeParam>::Item<'b>,
        ) -> anyhow::Result<()>,
{
    type FlowNode = FunctionNode<(HandleAll<Req>, T1, T2, T3), Self>;

    fn into_flow_node(self) -> Self::FlowNode {
        FunctionNode {
            f: self,
            marker: Default::default(),
        }
    }
}

impl<
        F: FnMut(HandleAll<Req>, T1, T2, T3) -> anyhow::Result<()>,
        Req: Serialize + DeserializeOwned,
        T1: NodeParam,
        T2: NodeParam,
        T3: NodeParam,
    > FlowNodeBase for FunctionNode<(HandleAll<Req>, T1, T2, T3), F>
where
    for<'a, 'b> &'a mut F: FnMut(HandleAll<Req>, T1, T2, T3) -> anyhow::Result<()>
        + FnMut(
            HandleAll<Req>,
            <T1 as NodeParam>::Item<'b>,
            <T2 as NodeParam>::Item<'b>,
            <T3 as NodeParam>::Item<'b>,
        ) -> anyhow::Result<()>,
{
    type Request = Req;

    fn imports(&mut self, ctx: &mut ImportCtx<'_>) {
        T1::imports(ctx);
        T2::imports(ctx);
        T3::imports(ctx);
    }

    fn emit(&mut self, requests: Vec<Self::Request>, ctx: &mut NodeCtx<'_>) -> anyhow::Result<()> {
        fn call_inner<Req: Serialize + DeserializeOwned, T1, T2, T3>(
            mut f: impl FnMut(HandleAll<Req>, T1, T2, T3) -> anyhow::Result<()>,
            requests: HandleAll<Req>,
            ctx_1: T1,
            ctx_2: T2,
            ctx_3: T3,
        ) -> Result<(), anyhow::Error> {
            f(requests, ctx_1, ctx_2, ctx_3)
        }

        call_inner(
            &mut self.f,
            HandleAll { requests },
            T1::retrieve(ctx.clone()),
            T2::retrieve(ctx.clone()),
            T3::retrieve(ctx.clone()),
        )
    }

    fn i_know_what_im_doing_with_this_manual_impl(&mut self) {}
}

mod node_params {
    use super::*;
    use serde::de::DeserializeOwned;

    pub struct HandleAll<T> {
        pub requests: Vec<T>,
    }

    pub struct DepOn<'a, N> {
        node: PhantomData<N>,
        ctx: NodeCtx<'a>,
    }

    impl<'a, N: FlowNodeBase + 'static> NodeParam for DepOn<'a, N> {
        type Item<'new> = DepOn<'new, N>;

        fn imports(ctx: &mut ImportCtx<'_>) {
            ctx.import::<N>();
        }

        fn retrieve(ctx: NodeCtx<'_>) -> Self::Item<'_> {
            DepOn {
                node: PhantomData,
                ctx: ctx.clone(),
            }
        }
    }

    impl<'a, N: FlowNodeBase> DepOn<'a, N> {
        /// Set a request on a particular node, simultaneously creating a new flowey
        /// Var in the process.
        #[track_caller]
        #[must_use]
        pub fn reqv<T, R>(&self, f: impl FnOnce(WriteVar<T>) -> R) -> ReadVar<T>
        where
            T: Serialize + DeserializeOwned,
            R: IntoRequest<Node = N> + 'static,
        {
            let (read, write) = self.ctx.new_var();
            self.ctx.req::<R>(f(write));
            read
        }
    }

    pub struct LegacyCtx<'a, ManualImports> {
        pub ctx: NodeCtx<'a>,
        imports: PhantomData<ManualImports>,
    }

    impl<'a, T1: FlowNodeBase + 'static> NodeParam for LegacyCtx<'a, (T1,)> {
        type Item<'new> = LegacyCtx<'new, (T1,)>;

        fn imports(ctx: &mut ImportCtx<'_>) {
            ctx.import::<T1>();
        }

        fn retrieve(ctx: NodeCtx<'_>) -> Self::Item<'_> {
            LegacyCtx {
                ctx: ctx.clone(),
                imports: PhantomData,
            }
        }
    }

    pub struct EmitRustStep<'ctx> {
        ctx: NodeCtx<'ctx>,
    }

    impl<'a> NodeParam for EmitRustStep<'a> {
        type Item<'new> = EmitRustStep<'new>;

        fn retrieve(ctx: NodeCtx<'_>) -> Self::Item<'_> {
            EmitRustStep { ctx: ctx.clone() }
        }
    }

    impl<'ctx> EmitRustStep<'ctx> {
        pub fn emit_rust_step<F, G>(&self, label: impl AsRef<str>, code: F) -> ReadVar<SideEffect>
        where
            F: for<'a> FnOnce(&'a mut StepCtx<'_>) -> G,
            G: for<'a> FnOnce(&'a mut RustRuntimeServices<'_>) -> anyhow::Result<()> + 'static,
        {
            self.ctx.emit_rust_step(label, code)
        }

        /// Emit a Rust-based step, creating a new `ReadVar<T>` from the step's
        /// return value.
        ///
        /// The var returned by this method is _not secret_. In order to create
        /// secret variables, use the `ctx.new_var_secret()` method.
        ///
        /// This is a convenience function that streamlines the following common
        /// flowey pattern:
        ///
        /// ```ignore
        /// // creating a new Var explicitly
        /// let (read_foo, write_foo) = ctx.new_var();
        /// ctx.emit_rust_step("foo", |ctx| {
        ///     let write_foo = write_foo.claim(ctx);
        ///     |rt| {
        ///         rt.write(write_foo, &get_foo());
        ///         Ok(())
        ///     }
        /// });
        ///
        /// // creating a new Var automatically
        /// let read_foo = ctx.emit_rust_stepv("foo", |ctx| |rt| get_foo());
        /// ```
        #[must_use]
        pub fn emit_rust_stepv<T, F, G>(&self, label: impl AsRef<str>, code: F) -> ReadVar<T>
        where
            T: Serialize + DeserializeOwned + 'static,
            F: for<'a> FnOnce(&'a mut StepCtx<'_>) -> G,
            G: for<'a> FnOnce(&'a mut RustRuntimeServices<'_>) -> anyhow::Result<T> + 'static,
        {
            self.ctx.emit_rust_stepv(label, code)
        }
    }
}

new_flow_node_base!(fn download_uefi_mu_msvm);

pub fn download_uefi_mu_msvm(
    requests: HandleAll<Request>,
    mut legacy_ctx: LegacyCtx<'_, (flowey_lib_common::install_dist_pkg::Node,)>,
    rstep: EmitRustStep<'_>,
    download_gh_release: DepOn<'_, flowey_lib_common::download_gh_release::Node>,
) -> anyhow::Result<()> {
    let mut version = None;
    let mut reqs: BTreeMap<MuMsvmArch, Vec<WriteVar<PathBuf>>> = BTreeMap::new();

    for req in requests.requests {
        match req {
            Request::Version(v) => same_across_all_reqs("Version", &mut version, v)?,
            Request::GetMsvmFd { arch, msvm_fd } => reqs.entry(arch).or_default().push(msvm_fd),
        }
    }

    let version = version.ok_or(anyhow::anyhow!("Missing essential request: Version"))?;

    // -- end of req processing -- //

    if reqs.is_empty() {
        return Ok(());
    }

    let extract_zip_deps =
        flowey_lib_common::_util::extract::extract_zip_if_new_deps(&mut legacy_ctx.ctx);

    for (arch, out_vars) in reqs {
        let file_name = match arch {
            MuMsvmArch::X86_64 => "RELEASE-X64-artifacts.zip",
            MuMsvmArch::Aarch64 => "RELEASE-AARCH64-artifacts.zip",
        };

        let mu_msvm_zip =
            download_gh_release.reqv(|v| flowey_lib_common::download_gh_release::Request {
                repo_owner: "microsoft".into(),
                repo_name: "mu_msvm".into(),
                needs_auth: false,
                tag: format!("v{version}"),
                file_name: file_name.into(),
                path: v,
            });

        let zip_file_version = format!("{version}-{file_name}");

        rstep.emit_rust_step(
            {
                format!(
                    "unpack mu_msvm package ({})",
                    match arch {
                        MuMsvmArch::X86_64 => "x64",
                        MuMsvmArch::Aarch64 => "aarch64",
                    },
                )
            },
            |ctx| {
                let extract_zip_deps = extract_zip_deps.clone().claim(ctx);
                let out_vars = out_vars.claim(ctx);
                let mu_msvm_zip = mu_msvm_zip.claim(ctx);
                move |rt| {
                    let mu_msvm_zip = rt.read(mu_msvm_zip);

                    let extract_dir = flowey_lib_common::_util::extract::extract_zip_if_new(
                        rt,
                        extract_zip_deps,
                        &mu_msvm_zip,
                        &zip_file_version,
                    )?;

                    let msvm_fd = extract_dir.join("FV/MSVM.fd");

                    for var in out_vars {
                        rt.write(var, &msvm_fd)
                    }

                    Ok(())
                }
            },
        );
    }

    Ok(())
}
