use anyhow::{bail, Context, Result};
use integration::helpers::{setup_client, ClientSetup};
use miden_client::store::NoteFilter;
use miden_client::ClientError;
use miden_objects::account::AccountId;
use miden_objects::address::{Address, AddressId, NetworkId};

const DEFAULT_ACCOUNT_ADDR: &str = "mtst1arjfa7ypxgq9jqzwtrdj6a5uwcscrxsq";
const DEFAULT_FAUCET_ADDR: &str = "mtst1arxgrnv5d3hcuyq3xp32s2ktkst5s5hq_qruqqypuyph";

fn parse_account_id(address: &str) -> Result<(NetworkId, AccountId, Address)> {
    let (network_id, decoded) =
        Address::decode(address).context("Failed to decode bech32 address")?;
    let account_id = match decoded.id() {
        AddressId::AccountId(id) => id,
        _ => bail!("Address is not an account ID"),
    };
    Ok((network_id, account_id, decoded))
}

#[tokio::main]
async fn main() -> Result<()> {
    let mut args = std::env::args().skip(1);
    let account_addr = args.next().unwrap_or_else(|| DEFAULT_ACCOUNT_ADDR.to_string());
    let faucet_addr = args.next().unwrap_or_else(|| DEFAULT_FAUCET_ADDR.to_string());

    let (account_net, account_id, account_address) = parse_account_id(&account_addr)
        .with_context(|| format!("Invalid account address: {}", account_addr))?;
    let (faucet_net, faucet_id, _faucet_address) = parse_account_id(&faucet_addr)
        .with_context(|| format!("Invalid faucet address: {}", faucet_addr))?;

    if account_net != faucet_net {
        bail!(
            "Network mismatch: account is {:?}, faucet is {:?}",
            account_net,
            faucet_net
        );
    }

    let ClientSetup { mut client, .. } = setup_client().await?;

    // Track address tag so notes addressed to this account are discoverable.
    match client.add_address(account_address, account_id).await {
        Ok(()) => {},
        Err(ClientError::AddressAlreadyTracked(_)) => {},
        Err(err) => return Err(err.into()),
    }

    let sync_summary = client.sync_state().await?;
    println!("Latest block: {}", sync_summary.block_num);

    let input_notes = client
        .get_input_notes(NoteFilter::Unspent)
        .await
        .context("Failed to fetch input notes")?;

    let mut matching = vec![];
    for note in input_notes {
        let mut amount = None;
        for asset in note.assets().iter_fungible() {
            if asset.faucet_id() == faucet_id {
                amount = Some(asset.amount());
            }
        }
        if let Some(amount) = amount {
            matching.push((note.id(), amount, note.state().clone()));
        }
    }

    println!("Account address: {}", account_addr);
    println!("Faucet address: {}", faucet_addr);
    if matching.is_empty() {
        println!("No unspent notes found for this faucet.");
    } else {
        println!("Unspent notes for faucet:");
        for (id, amount, state) in matching {
            println!("  note={} amount={} state={:?}", id.to_hex(), amount, state);
        }
    }

    Ok(())
}
