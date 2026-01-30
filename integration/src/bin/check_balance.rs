use anyhow::{bail, Context, Result};
use integration::helpers::{setup_client, ClientSetup};
use miden_objects::account::AccountId;
use miden_objects::address::{Address, AddressId, NetworkId};

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

    let mut account_record = client.get_account(account_id).await?;
    if account_record.is_none() {
        client
            .import_account_by_id(account_id)
            .await
            .context("Failed to import account by ID")?;
        client.sync_state().await?;
        account_record = client.get_account(account_id).await?;
    }

    let account_record = account_record
        .ok_or_else(|| anyhow::anyhow!("Account not found after import"))?;

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
