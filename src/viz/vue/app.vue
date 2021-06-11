<template>
    <div class="document-area">
        <benchmark-list-pane ref="benchmarks"/>
        <proof-trace-pane ref="proofTrace"/>
    </div>
</template>

<script>
import BenchmarkListPane from './benchmark-list-pane.vue';
import ProofTracePane from './proof-trace-pane.vue';

export default {
    components: { ProofTracePane, BenchmarkListPane }
}
</script>