import * as hub from "@huggingface/hub";

async function getDataset() {
    const repoId: hub.RepoId = {
        name: "quinn-dougherty/fvapps",
        type: "dataset",
    };
    const files = await hub.listFiles(repoId);
    return await files;
}

export { getDataset };
