use vstd::prelude::*;

verus! {

// =====================================================================
// 1. THE MATHEMATICAL SPECIFICATION (GHOST CODE)
// =====================================================================
// ADDED 'pub open' HERE:
pub open spec fn is_valid_mutation(target: u64, prime_q: u64) -> bool {
    // The Exact-Cover Matrix Constraint
    prime_q > 1 && target > prime_q && (target % prime_q == 0)
}

// =====================================================================
// 2. THE STATE MACHINE (THE ACCUMULATOR)
// =====================================================================
pub struct TelemetryState {
    pub active_payload: u64,
    pub packets_processed: u64,
}

impl TelemetryState {

    // =================================================================
    // 3. THE VERIFIED eBPF TRANSITION (EXECUTABLE CODE)
    // =================================================================
    pub fn apply_telemetry(&mut self, incoming_target: u64, prime_q: u64)
        requires 
            // Preconditions for the hardware state
            prime_q > 1,
            incoming_target > prime_q,
            old(self).packets_processed < 0xFFFF_FFFF_FFFF_FFFF, // Prevent overflow
        ensures 
            // THE MATHEMATICAL LOCK:
            self.active_payload == 
                if is_valid_mutation(incoming_target, prime_q) { 
                    incoming_target 
                } else { 
                    old(self).active_payload 
                },
            
            // We also prove that the counter always strictly increments
            self.packets_processed == old(self).packets_processed + 1,
    {
        // --- BARE METAL EXECUTION START ---
        
        // The single 10-cycle CPU instruction that protects the state
        if incoming_target % prime_q == 0 {
            self.active_payload = incoming_target;
        }

        self.packets_processed = self.packets_processed + 1;
        
        // --- BARE METAL EXECUTION END ---
    }
}

// =====================================================================
// 4. THE ENTRY POINT
// =====================================================================
pub fn main() {
    // The Verus compiler will verify the exact-cover matrix logic above,
    // and then cleanly exit here.
}

} // end verus! macro