use integration::helpers::{
    build_project_in_dir, create_testing_account_from_package, create_testing_note_from_package,
    AccountCreationConfig, NoteCreationConfig,
};

use miden_client::transaction::OutputNote;
use miden_core::Felt;
use miden_testing::{Auth, MockChain};
use std::{path::Path, sync::Arc};

#[tokio::test]
async fn higher_than_seven_true() -> anyhow::Result<()> {
    let mut builder = MockChain::builder();
    let sender = builder.add_existing_wallet(Auth::BasicAuth)?;

    let account_package = Arc::new(build_project_in_dir(
        Path::new("../contracts/betting-account"),
        true,
    )?);
    let note_package = Arc::new(build_project_in_dir(
        Path::new("../contracts/higher-than-seven-note"),
        true,
    )?);

    let account = create_testing_account_from_package(
        account_package.clone(),
        AccountCreationConfig::default(),
    )
    .await?;

    let note_config = NoteCreationConfig {
        inputs: vec![Felt::new(8), Felt::new(1)],
        ..Default::default()
    };
    let note = create_testing_note_from_package(note_package.clone(), sender.id(), note_config)?;

    builder.add_account(account.clone())?;
    builder.add_output_note(OutputNote::Full(note.clone().into()));

    let mut mock_chain = builder.build()?;
    let tx_context = mock_chain
        .build_tx_context(account.id(), &[note.id()], &[])?
        .build()?;

    let executed_transaction = tx_context.execute().await?;
    mock_chain.add_pending_executed_transaction(&executed_transaction)?;
    mock_chain.prove_next_block()?;

    Ok(())
}

#[tokio::test]
async fn higher_than_seven_false() -> anyhow::Result<()> {
    let mut builder = MockChain::builder();
    let sender = builder.add_existing_wallet(Auth::BasicAuth)?;

    let account_package = Arc::new(build_project_in_dir(
        Path::new("../contracts/betting-account"),
        true,
    )?);
    let note_package = Arc::new(build_project_in_dir(
        Path::new("../contracts/higher-than-seven-note"),
        true,
    )?);

    let account = create_testing_account_from_package(
        account_package.clone(),
        AccountCreationConfig::default(),
    )
    .await?;

    let note_config = NoteCreationConfig {
        inputs: vec![Felt::new(7), Felt::new(0)],
        ..Default::default()
    };
    let note = create_testing_note_from_package(note_package.clone(), sender.id(), note_config)?;

    builder.add_account(account.clone())?;
    builder.add_output_note(OutputNote::Full(note.clone().into()));

    let mut mock_chain = builder.build()?;
    let tx_context = mock_chain
        .build_tx_context(account.id(), &[note.id()], &[])?
        .build()?;

    let executed_transaction = tx_context.execute().await?;
    mock_chain.add_pending_executed_transaction(&executed_transaction)?;
    mock_chain.prove_next_block()?;

    Ok(())
}
