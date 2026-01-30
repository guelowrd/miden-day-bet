use anyhow::{bail, Context, Result};
use integration::helpers::{setup_client, ClientSetup};
use miden_client::store::NoteFilter;
use miden_client::transaction::TransactionRequestBuilder;
use miden_client::ClientError;
use miden_objects::account::AccountId;
use miden_objects::address::{Address, AddressId, NetworkId};

const DEFAULT_ACCOUNT_ADDR: &str = "mtst1arnsh08awzplyqqgpm2fxk426ux59t6d";
const DEFAULT_FAUCET_ADDR: &str = "mtst1ap2t7nsjausqsgrswk9syfzkcu328yna";

fn parse_account_id(address: &str) -> Result<(NetworkId, AccountId, Address)> {
    let (network_id, decoded) =
        Address::decode(address).context("Failed to decode bech32 address")?;
    let account_id = match decoded.id() {
        AddressId::AccountId(id) => id,
        _ => bail!("Address is not an account ID"),
    };
    Ok((network_id, account_id, decoded))
}

fn parse_optional_account_id(address: &str) -> Result<(NetworkId, AccountId)> {
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
    let account_addr = args.next().unwrap_or_else(|| DEFAULT_ACCOUNT_ADDR.to_string());
    let faucet_addr = args.next();

    let (account_net, account_id, account_address) = parse_account_id(&account_addr)
        .with_context(|| format!("Invalid account address: {}", account_addr))?;

    let faucet_id = if let Some(faucet_addr) = &faucet_addr {
        let (faucet_net, faucet_id) = parse_optional_account_id(faucet_addr)
            .with_context(|| format!("Invalid faucet address: {}", faucet_addr))?;
        if account_net != faucet_net {
            bail!(
                "Network mismatch: account is {:?}, faucet is {:?}",
                account_net,
                faucet_net
            );
        }
        Some(faucet_id)
    } else {
        None
    };

    let ClientSetup { mut client, .. } = setup_client().await?;

    // Track address tag so notes addressed to this account are discoverable.
    match client.add_address(account_address, account_id).await {
        Ok(()) => {},
        Err(ClientError::AddressAlreadyTracked(_)) => {},
        Err(err) => return Err(err.into()),
    }

    let sync_summary = client.sync_state().await?;
    println!("Latest block: {}", sync_summary.block_num);

    // Ensure account is tracked locally.
    if client.get_account(account_id).await?.is_none() {
        client.import_account_by_id(account_id).await?;
        client.sync_state().await?;
    }

    let input_notes = client
        .get_input_notes(NoteFilter::Unspent)
        .await
        .context("Failed to fetch input notes")?;

    let mut note_ids = vec![];
    for note in input_notes {
        if let Some(faucet_id) = faucet_id {
            let mut has_faucet = false;
            for asset in note.assets().iter_fungible() {
                if asset.faucet_id() == faucet_id {
                    has_faucet = true;
                    break;
                }
            }
            if !has_faucet {
                continue;
            }
        }
        note_ids.push(note.id());
    }

    println!("Account address: {}", account_addr);
    if let Some(faucet_addr) = &faucet_addr {
        println!("Faucet address: {}", faucet_addr);
    }

    if note_ids.is_empty() {
        println!("No unspent notes found.");
        return Ok(());
    }

    let request = TransactionRequestBuilder::new()
        .authenticated_input_notes(note_ids.iter().map(|id| (*id, None)))
        .build()
        .context("Failed to build consume-notes request")?;

    let tx_id = client
        .submit_new_transaction(account_id, request)
        .await
        .context("Failed to submit consume-notes transaction")?;

    println!("Consume tx ID: {}", tx_id.to_hex());
    for id in note_ids {
        println!("  consumed note: {}", id.to_hex());
    }

    Ok(())
}
