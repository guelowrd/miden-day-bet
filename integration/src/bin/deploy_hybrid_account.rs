use integration::helpers::{
    build_project_in_dir, create_hybrid_wallet_account_from_package, setup_client,
    AccountCreationConfig, ClientSetup,
};

use anyhow::{Context, Result};
use miden_objects::address::NetworkId;
use std::{path::Path, sync::Arc};

#[tokio::main]
async fn main() -> Result<()> {
    // Instantiate client
    let ClientSetup {
        mut client,
        keystore,
    } = setup_client().await?;

    let sync_summary = client.sync_state().await?;
    println!("Latest block: {}", sync_summary.block_num);

    // Build betting account contract
    let betting_path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../contracts/betting-account");
    let betting_package = Arc::new(
        build_project_in_dir(&betting_path, true)
            .context("Failed to build betting account contract")?,
    );

    let cfg = AccountCreationConfig::default();
    let account = create_hybrid_wallet_account_from_package(
        &mut client,
        keystore,
        betting_package,
        cfg,
    )
    .await
    .context("Failed to create hybrid account")?;

    let account_hex = account.id().to_hex();
    let account_bech32 = account.id().to_bech32(NetworkId::Testnet);

    println!("Hybrid account ID (hex): {}", account_hex);
    println!("Hybrid account address: {}", account_bech32);

    Ok(())
}
