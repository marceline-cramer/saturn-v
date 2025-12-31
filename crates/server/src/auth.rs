// Copyright (C) 2025 Marceline Cramer
// SPDX-License-Identifier: AGPL-3.0-or-later
//
// Saturn V is free software: you can redistribute it and/or modify it under
// the terms of the GNU Affero General Public License as published by the Free
// Software Foundation, either version 3 of the License, or (at your option) any
// later version.
//
// Saturn V is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
// FOR A PARTICULAR PURPOSE. See the GNU Affero General Public License for
// more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with Saturn V. If not, see <https://www.gnu.org/licenses/>.

use std::{
    collections::BTreeMap,
    str::FromStr,
    time::{SystemTime, UNIX_EPOCH},
};

use base64::{engine::general_purpose::URL_SAFE_NO_PAD, Engine as _};
use rand::RngCore;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::db::{CommitDataflow, FjallTransaction, Key};
use saturn_v_protocol::{ServerError, ServerResult};

pub const SESSION_COOKIE: &str = "saturn_v_session";
pub const CSRF_HEADER: &str = "x-saturn-v-csrf";

#[derive(Clone, Debug)]
pub struct AuthConfig {
    pub admin_password: Option<String>,
    pub session_ttl_secs: u64,
    pub token_ttl_secs: u64,
    pub cookie_secure: bool,
    pub cookie_samesite: CookieSameSite,
}

impl Default for AuthConfig {
    fn default() -> Self {
        Self {
            admin_password: None,
            session_ttl_secs: 60 * 60 * 24 * 30,
            token_ttl_secs: 60 * 60 * 24 * 365,
            cookie_secure: true,
            cookie_samesite: CookieSameSite::Lax,
        }
    }
}

impl AuthConfig {
    pub fn enabled(&self) -> bool {
        self.admin_password.is_some()
    }

    pub fn check_password(&self, password: &str) -> bool {
        self.admin_password
            .as_deref()
            .is_some_and(|expected| expected == password)
    }

    pub fn cookie_header_value(&self, session_id: &str) -> String {
        let mut parts = vec![
            format!("{SESSION_COOKIE}={session_id}"),
            "Path=/".to_string(),
            "HttpOnly".to_string(),
            format!("SameSite={}", self.cookie_samesite.as_str()),
        ];

        if self.cookie_secure {
            parts.push("Secure".to_string());
        }

        parts.join("; ")
    }

    pub fn clear_cookie_header_value(&self) -> String {
        let mut parts = vec![
            format!("{SESSION_COOKIE}="),
            "Path=/".to_string(),
            "HttpOnly".to_string(),
            "Max-Age=0".to_string(),
            format!("SameSite={}", self.cookie_samesite.as_str()),
        ];

        if self.cookie_secure {
            parts.push("Secure".to_string());
        }

        parts.join("; ")
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum CookieSameSite {
    Lax,
    Strict,
    None,
}

impl FromStr for CookieSameSite {
    type Err = String;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        match input.to_ascii_lowercase().as_str() {
            "strict" => Ok(CookieSameSite::Strict),
            "none" => Ok(CookieSameSite::None),
            "lax" => Ok(CookieSameSite::Lax),
            other => Err(format!("invalid SameSite value: {other}")),
        }
    }
}

impl CookieSameSite {
    pub fn as_str(self) -> &'static str {
        match self {
            CookieSameSite::Lax => "Lax",
            CookieSameSite::Strict => "Strict",
            CookieSameSite::None => "None",
        }
    }
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct AuthSessions(pub BTreeMap<String, SessionRecord>);

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct AuthTokens(pub BTreeMap<String, TokenRecord>);

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct SessionRecord {
    pub csrf: String,
    pub expires_at: u64,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct TokenRecord {
    pub expires_at: u64,
}

#[derive(Clone, Debug)]
pub struct TokenGrant<'a> {
    pub password: Option<&'a str>,
    pub bearer: Option<&'a str>,
    pub session: Option<&'a str>,
    pub csrf: Option<&'a str>,
}

#[derive(Clone, Debug)]
pub struct LogoutRequest<'a> {
    pub session: &'a str,
    pub csrf: Option<&'a str>,
}

#[derive(Clone, Debug)]
pub struct AuthRequest<'a> {
    pub bearer: Option<&'a str>,
    pub session: Option<&'a str>,
    pub csrf: Option<&'a str>,
    pub require_csrf: bool,
}

pub fn login<D: CommitDataflow>(
    tx: &mut FjallTransaction<D>,
    config: &AuthConfig,
    password: &str,
) -> ServerResult<(String, String)> {
    if !config.enabled() {
        return Err(ServerError::Unauthorized);
    }

    if !config.check_password(password) {
        return Err(ServerError::Unauthorized);
    }

    let mut sessions = load_sessions(tx)?;
    prune_sessions(&mut sessions);

    let session_id = random_secret();
    let csrf = random_secret();
    let record = SessionRecord {
        csrf: csrf.clone(),
        expires_at: now_epoch().saturating_add(config.session_ttl_secs),
    };

    sessions.0.insert(session_id.clone(), record);
    store_sessions(tx, &sessions)?;

    let cookie = config.cookie_header_value(&session_id);
    Ok((cookie, csrf))
}

pub fn issue_token<D: CommitDataflow>(
    tx: &mut FjallTransaction<D>,
    config: &AuthConfig,
    grant: TokenGrant<'_>,
) -> ServerResult<String> {
    if !config.enabled() {
        return Err(ServerError::Unauthorized);
    }

    let mut tokens = load_tokens(tx)?;
    prune_tokens(&mut tokens);

    let authorized =
        if grant.password.is_some_and(|pw| config.check_password(pw)) {
            true
        } else if grant
            .bearer
            .is_some_and(|token| validate_token_internal(&tokens, token))
        {
            true
        } else if let Some(session_id) = grant.session {
            let mut sessions = load_sessions(tx)?;
            let sessions_dirty = prune_sessions(&mut sessions);
            let authorized = sessions.0.get(session_id).is_some_and(|session| {
                match (grant.csrf, &session.csrf) {
                    (Some(csrf), expected) if csrf == expected => true,
                    (Some(_), _) => false,
                    _ => false,
                }
            });

            if sessions_dirty {
                store_sessions(tx, &sessions)?;
            }

            authorized
        } else {
            false
        };

    if !authorized {
        return Err(ServerError::Unauthorized);
    }

    let token = random_secret();
    let hash = hash_secret(&token);
    let record = TokenRecord {
        expires_at: now_epoch().saturating_add(config.token_ttl_secs),
    };

    tokens.0.insert(hash, record);
    store_tokens(tx, &tokens)?;

    Ok(token)
}

pub fn logout<D: CommitDataflow>(
    tx: &mut FjallTransaction<D>,
    config: &AuthConfig,
    request: LogoutRequest<'_>,
) -> ServerResult<String> {
    if !config.enabled() {
        return Err(ServerError::Unauthorized);
    }

    let mut sessions = load_sessions(tx)?;
    prune_sessions(&mut sessions);

    let Some(record) = sessions.0.get(request.session) else {
        return Err(ServerError::Unauthorized);
    };

    if record.csrf != request.csrf.unwrap_or_default() {
        return Err(ServerError::Forbidden);
    }

    sessions.0.remove(request.session);
    store_sessions(tx, &sessions)?;

    Ok(config.clear_cookie_header_value())
}

pub fn authorize<D: CommitDataflow>(
    tx: &mut FjallTransaction<D>,
    config: &AuthConfig,
    request: AuthRequest<'_>,
) -> ServerResult<()> {
    if !config.enabled() {
        return Ok(());
    }

    if let Some(token) = request.bearer {
        let mut tokens = load_tokens(tx)?;
        let dirty = prune_tokens(&mut tokens);
        let valid = validate_token_internal(&tokens, token);
        if dirty {
            store_tokens(tx, &tokens)?;
        }
        return if valid {
            Ok(())
        } else {
            Err(ServerError::Unauthorized)
        };
    }

    if let Some(session_id) = request.session {
        let mut sessions = load_sessions(tx)?;
        let dirty = prune_sessions(&mut sessions);
        let result = sessions.0.get(session_id).map(|session| {
            if request.require_csrf {
                match request.csrf {
                    Some(csrf) if csrf == session.csrf => Ok(()),
                    Some(_) => Err(ServerError::Forbidden),
                    None => Err(ServerError::Forbidden),
                }
            } else {
                Ok(())
            }
        });

        if dirty {
            store_sessions(tx, &sessions)?;
        }

        return result.unwrap_or(Err(ServerError::Unauthorized));
    }

    Err(ServerError::Unauthorized)
}

fn load_sessions<D: CommitDataflow>(tx: &mut FjallTransaction<D>) -> ServerResult<AuthSessions> {
    Ok(tx.get(&Key::AuthSessions)?.unwrap_or_default())
}

fn store_sessions<D: CommitDataflow>(
    tx: &mut FjallTransaction<D>,
    sessions: &AuthSessions,
) -> ServerResult<()> {
    tx.insert(&Key::AuthSessions, sessions)
}

fn load_tokens<D: CommitDataflow>(tx: &mut FjallTransaction<D>) -> ServerResult<AuthTokens> {
    Ok(tx.get(&Key::AuthTokens)?.unwrap_or_default())
}

fn store_tokens<D: CommitDataflow>(
    tx: &mut FjallTransaction<D>,
    tokens: &AuthTokens,
) -> ServerResult<()> {
    tx.insert(&Key::AuthTokens, tokens)
}

fn prune_sessions(sessions: &mut AuthSessions) -> bool {
    let now = now_epoch();
    let before = sessions.0.len();
    sessions.0.retain(|_, session| session.expires_at > now);
    before != sessions.0.len()
}

fn prune_tokens(tokens: &mut AuthTokens) -> bool {
    let now = now_epoch();
    let before = tokens.0.len();
    tokens.0.retain(|_, token| token.expires_at > now);
    before != tokens.0.len()
}

fn validate_token_internal(tokens: &AuthTokens, bearer: &str) -> bool {
    let hash = hash_secret(bearer);
    tokens.0.contains_key(&hash)
}

pub fn now_epoch() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs()
}

pub fn random_secret() -> String {
    let mut bytes = [0u8; 32];
    rand::rngs::OsRng.fill_bytes(&mut bytes);
    URL_SAFE_NO_PAD.encode(bytes)
}

pub fn hash_secret(secret: &str) -> String {
    let digest = Sha256::digest(secret.as_bytes());
    URL_SAFE_NO_PAD.encode(digest)
}
