use integration::helpers::{
    build_project_in_dir, create_account_from_package, setup_client, AccountCreationConfig,
    ClientSetup,
};

use anyhow::{Context, Result};
use miden_objects::address::NetworkId;
use std::{path::Path, sync::Arc};

#[tokio::main]
async fn main() -> Result<()> {
    // Instantiate client
    let ClientSetup { mut client, .. } = setup_client().await?;

    let sync_summary = client.sync_state().await?;
    println!("Latest block: {}", sync_summary.block_num);

    // Build betting account contract
    let betting_path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../contracts/betting-account");
    let betting_package = Arc::new(
        build_project_in_dir(&betting_path, true)
            .context("Failed to build betting account contract")?,
    );

    // Create the betting account (no special storage required)
    let betting_cfg = AccountCreationConfig::default();
    let betting_account =
        create_account_from_package(&mut client, betting_package.clone(), betting_cfg)
            .await
            .context("Failed to create betting account")?;

    let betting_hex = betting_account.id().to_hex();
    let betting_bech32 = betting_account.id().to_bech32(NetworkId::Testnet);

    println!("Betting account ID (hex): {}", betting_hex);
    println!("Betting account address: {}", betting_bech32);

    Ok(())
}
