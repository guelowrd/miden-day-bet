use integration::helpers::{
    build_project_in_dir, create_account_from_package, create_basic_wallet_account,
    create_note_from_package, setup_client, AccountCreationConfig, ClientSetup, NoteCreationConfig,
};

use anyhow::{Context, Result};
use miden_client::{transaction::OutputNote, transaction::TransactionRequestBuilder, Felt};
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

    // Build contracts
    let betting_path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../contracts/betting-account");
    let betting_package = Arc::new(
        build_project_in_dir(&betting_path, true)
            .context("Failed to build betting account contract")?,
    );
    let note_path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../contracts/higher-than-seven-note");
    let note_package = Arc::new(
        build_project_in_dir(&note_path, true)
            .context("Failed to build higher-than-seven note contract")?,
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

    // Create a separate sender account using the BasicWallet component
    let sender_cfg = AccountCreationConfig::default();
    let sender_account = create_basic_wallet_account(&mut client, keystore.clone(), sender_cfg)
        .await
        .context("Failed to create sender wallet account")?;

    println!("Sender account ID (hex): {}", sender_account.id().to_hex());

    // Build higher-than-seven note with inputs: input_value, expected
    let mut note_cfg = NoteCreationConfig::default();
    note_cfg.inputs = vec![Felt::new(8), Felt::new(1)];

    let betting_note = create_note_from_package(
        &mut client,
        note_package.clone(),
        sender_account.id(),
        note_cfg,
    )
    .context("Failed to create higher-than-seven note from package")?;

    println!("Note hash: {}", betting_note.id().to_hex());

    // Publish the note
    let note_publish_request = TransactionRequestBuilder::new()
        .own_output_notes(vec![OutputNote::Full(betting_note.clone())])
        .build()
        .context("Failed to build note publish transaction request")?;

    let note_publish_tx_id = client
        .submit_new_transaction(sender_account.id(), note_publish_request)
        .await
        .context("Failed to create note publish transaction")?;

    println!("Note publish transaction ID: {}", note_publish_tx_id.to_hex());

    client
        .sync_state()
        .await
        .context("Failed to sync state after publishing note")?;

    // Consume the note with the betting account
    let consume_note_request = TransactionRequestBuilder::new()
        .unauthenticated_input_notes([(betting_note.clone(), None)])
        .build()
        .context("Failed to build consume note transaction request")?;

    let consume_tx_id = client
        .submit_new_transaction(betting_account.id(), consume_note_request)
        .await
        .context("Failed to create consume note transaction")?;

    println!("Consume transaction ID: {}", consume_tx_id.to_hex());

    Ok(())
}
