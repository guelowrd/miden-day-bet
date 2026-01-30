use anyhow::{bail, Context, Result};
use integration::helpers::{setup_client, ClientSetup};
use miden_client::transaction::TransactionRequestBuilder;
use miden_objects::account::AccountId;
use miden_objects::address::{Address, AddressId, NetworkId};
use miden_objects::note::NoteFile;

const DEFAULT_ACCOUNT_ADDR: &str = "mtst1arjfa7ypxgq9jqzwtrdj6a5uwcscrxsq";
const DEFAULT_FAUCET_ADDR: &str = "mtst1arxgrnv5d3hcuyq3xp32s2ktkst5s5hq_qruqqypuyph";

fn parse_account_id(address: &str) -> Result<(NetworkId, AccountId)> {
    let (network_id, decoded) =
        Address::decode(address).context("Failed to decode bech32 address")?;
    let account_id = match decoded.id() {
        AddressId::AccountId(id) => id,
        _ => bail!("Address is not an account ID"),
    };
    Ok((network_id, account_id))
}

#[tokio::main]
async fn main() -> Result<()> {
    let mut args = std::env::args().skip(1);
    let note_path = args
        .next()
        .unwrap_or_else(|| "../note (38).mno".to_string());
    let account_addr = args.next().unwrap_or_else(|| DEFAULT_ACCOUNT_ADDR.to_string());
    let faucet_addr = args.next().unwrap_or_else(|| DEFAULT_FAUCET_ADDR.to_string());

    let (account_net, account_id) = parse_account_id(&account_addr)
        .with_context(|| format!("Invalid account address: {}", account_addr))?;
    let (faucet_net, faucet_id) = parse_account_id(&faucet_addr)
        .with_context(|| format!("Invalid faucet address: {}", faucet_addr))?;

    if account_net != faucet_net {
        bail!(
            "Network mismatch: account is {:?}, faucet is {:?}",
            account_net,
            faucet_net
        );
    }

    let ClientSetup { mut client, .. } = setup_client().await?;
    client.sync_state().await?;

    let note_file =
        NoteFile::read(&note_path).with_context(|| format!("Failed to read note file: {}", note_path))?;

    let note_id = match &note_file {
        NoteFile::NoteId(id) => *id,
        NoteFile::NoteDetails { details, .. } => details.id(),
        NoteFile::NoteWithProof(note, _) => note.id(),
    };

    // Ensure account is tracked locally.
    if client.get_account(account_id).await?.is_none() {
        client.import_account_by_id(account_id).await?;
        client.sync_state().await?;
    }

    let request = match note_file {
        NoteFile::NoteWithProof(note, _) => TransactionRequestBuilder::new()
            .unauthenticated_input_notes([(note, None)])
            .build()
            .context("Failed to build consume-note request")?,
        other => {
            client
                .import_note(other)
                .await
                .context("Failed to import note into store")?;
            TransactionRequestBuilder::new()
                .authenticated_input_notes([(note_id, None)])
                .build()
                .context("Failed to build consume-note request")?
        },
    };

    let tx_id = client
        .submit_new_transaction(account_id, request)
        .await
        .context("Failed to submit consume-note transaction")?;

    println!("Note ID: {}", note_id.to_hex());
    println!("Consume tx ID: {}", tx_id.to_hex());

    client.sync_state().await?;

    let account_record = client
        .get_account(account_id)
        .await?
        .ok_or_else(|| anyhow::anyhow!("Account not found after consume"))?;

    let balance = account_record
        .account()
        .vault()
        .get_balance(faucet_id)
        .unwrap_or(0);

    println!("Account address: {}", account_addr);
    println!("Faucet address: {}", faucet_addr);
    println!("Balance: {}", balance);

    Ok(())
}
