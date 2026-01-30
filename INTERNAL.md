# Internal Notes

## Hybrid account deployment

- Use the hybrid account (BasicWallet + betting component) so faucet/public notes are accepted.
- Deploy command:
  
  ```bash
  cargo run -p integration --bin deploy_hybrid_account
  ```

- Send notes to the **bech32** account address printed by the deploy command.
- The hex account id is **16 bytes**; explorers may show 32-byte recipient values which do **not** match account ids.

## Faucet used in recent testing

- Faucet bech32: `mtst1ap2t7nsjausqsgrswk9syfzkcu328yna`

## Client utilities (integration/src/bin)

- `deploy_hybrid_account`: prints account bech32 + hex id
- `check_balance`: checks asset balance for a faucet
- `sync_list_notes`: syncs notes and lists matching assets
- `consume_note_file`: consumes a private note file
- `inspect_note_file`: prints note details, including faucet bech32
- `consume_unspent_notes`: attempts to consume any unspent notes in local store

## Known pitfalls

- If balance is unchanged after a public transfer, confirm the faucet id and account address are correct,
  then run `sync_list_notes`.
- If `consume_unspent_notes` errors with an MMR message, there are no usable unspent notes in the local store.
